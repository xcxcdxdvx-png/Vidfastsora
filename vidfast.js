/* ==========================================================================
 * Sora module for https://vidfast.vc  (movies + TV shows, HLS, multi-server)
 * --------------------------------------------------------------------------
 * Async JS mode (asyncJS: true)
 *   searchResults(keyword)   -> JSON string: [{ title, image, href }]
 *   extractDetails(url)      -> JSON string: [{ description, aliases, airdate }]
 *   extractEpisodes(url)     -> JSON string: [{ href, number }]   (number = Int!)
 *   extractStreamUrl(url)    -> JSON string: { streams: [{ streamUrl, title, headers }] }
 *
 * Only fetchv2 / atob / btoa / console exist inside Sora's JavaScriptCore.
 * No DOM, no Node API, no WebCrypto, no setTimeout.
 *
 * What this module does
 * ---------------------
 * vidfast does not expose a public API. Its player talks to an obfuscated
 * endpoint (/APA91cut.../a/<endpoint>/<payload>) where every payload is a
 * custom "VF1" frame:
 *
 *     base64url-custom( seed4 || permute( TLV blob ) )
 *     TLV blob = magic "VF1", version, variant, buildId, kind,
 *                plaintext length, salt(16), nonce(12),
 *                AES-256-GCM ciphertext, GCM tag(16)
 *     key       = HKDF-SHA256(IKM, salt, "vidfast/v1/aes-256-gcm\0" || sha256(head))
 *     AAD       = TLV 1..6 ("head")
 *     permutation is a Fisher-Yates shuffle driven by an xorshift32 PRNG
 *     seeded with sha256("vidfast/v1/frame-permutation\0" || IKM || seed4 || len)
 *
 * The server ticket that is returned by the bootstrap call is wrapped in a
 * second, lighter transform (byte rotation/xor/add + permutation) before it is
 * sent to the /servers endpoint.
 *
 * Everything above is re-implemented in plain JS below (SHA-256, HMAC, HKDF,
 * AES-256-GCM, the custom base64 alphabet, the PRNG, both transforms), so no
 * obfuscated player code ships with this module.
 *
 * Per-server streams
 * ------------------
 * The /servers call returns 5 source descriptors (vRapid, vBlaze, Cobra, Bravo,
 * Delta). Each is resolved separately through /stream and yields a signed,
 * expiring HLS URL on a rotating CDN. They are returned as 5 Sora "streams",
 * which is exactly what Sora's server picker displays.
 *
 * Metadata (keyless)
 * ------------------
 * Search uses the public IMDb suggestion endpoint, episodes come from TVMaze
 * (free, no key). Movie/series blurbs come from TVMaze or Wikipedia. TMDB is
 * only used by Sora itself (by title) for posters/backdrops.
 *
 * Rotation
 * --------
 * vidfast rebuilds its bundle regularly, which changes the build id / prefix /
 * manifest hash. The constants below are baked in, but when the API rejects
 * them the module re-reads the live player chunk from vidfast and rebuilds the
 * config at runtime (see vidfastDiscoverConfig). Only the "variant 1" protocol
 * is implemented; if vidfast ever retires it, the module needs an update.
 * ========================================================================== */

var VIDFAST_ORIGIN = "https://vidfast.vc";
var VIDFAST_REFERER = "https://vidfast.vc/";

var VIDFAST_UA = "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/137.0.0.0 Safari/537.36";
var VIDFAST_META_UA = "SoraVidfastModule/1.0 (+https://github.com/box_sheets/sora-modules)";

/* Baked-in protection config (verified 2026-11-22). */
var VIDFAST_STATIC_CONFIG = {
  prefix: "/APA91cutEYiePKFryx41DSH1q9JjstDOtXHVsK6O7vt0iGZX8gP3FuNc5XQWCbAiI-ZK31UqWpJ0wOrh3kD5YAtMkhuq9LGjEz5sg881zlqiT9YfB8s_B5a1VvjU89ntW1YQuD9n82FHVz5lv8hUgk2AbcCMjlAnEROu6Oy_VEemc5gSRkbGtoa/a",
  buildId: "8rGefdRb2G-BTMM0lBAGdBh4L3KzbIrX_btZOXsNxjc",
  alphabet62: "KXpN7W3G9CojEd825gusxeFMOJfYiVhcytIRmDnkTw4rS60HzAlQqZU1bLBaPv",
  ikm: "d03304ba1ec687f329b52726c27b78422b703ca7ae3afe96a4d025eae7cec64c",
  endpoints: { bootstrap: "I1RWxE1QOtg", servers: "2sYX823A4fc", stream: "8ZFavsHEv8c" }
};

/* ==========================================================================
 * 1. Protocol core (pure JS, no WebCrypto)
 * ========================================================================== */

var VF = (function () {
  "use strict";

  var CFG = {
    prefix: "", buildId: "", alphabet62: "", ikm: "",
    endpoints: { bootstrap: "", servers: "", stream: "" },
    ikm_bytes: new Uint8Array(0)
  };

  /* ------------------------------------------------------------- bytes */

  function hexToBytes(h) {
    var out = new Uint8Array(h.length >> 1), i;
    for (i = 0; i < out.length; i++) out[i] = parseInt(h.substr(i * 2, 2), 16);
    return out;
  }

  function bytesToHex(b) {
    var out = "", i, t;
    for (i = 0; i < b.length; i++) {
      t = b[i].toString(16);
      out += t.length < 2 ? "0" + t : t;
    }
    return out;
  }

  function utf8Encode(str) {
    var out = [], i, c, d;
    for (i = 0; i < str.length; i++) {
      c = str.charCodeAt(i);
      if (c < 0x80) out.push(c);
      else if (c < 0x800) out.push(0xc0 | (c >> 6), 0x80 | (c & 63));
      else if (c >= 0xd800 && c <= 0xdbff && i + 1 < str.length) {
        d = str.charCodeAt(i + 1);
        if (d >= 0xdc00 && d <= 0xdfff) {
          c = 0x10000 + ((c - 0xd800) << 10) + (d - 0xdc00);
          i++;
          out.push(0xf0 | (c >> 18), 0x80 | ((c >> 12) & 63), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63));
        } else out.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63));
      } else out.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63));
    }
    return new Uint8Array(out);
  }

  function utf8Decode(bytes) {
    var out = "", i = 0, c, c2, c3, c4;
    while (i < bytes.length) {
      c = bytes[i++];
      if (c < 0x80) out += String.fromCharCode(c);
      else if (c < 0xe0) out += String.fromCharCode(((c & 31) << 6) | (bytes[i++] & 63));
      else if (c < 0xf0) {
        c2 = bytes[i++]; c3 = bytes[i++];
        out += String.fromCharCode(((c & 15) << 12) | ((c2 & 63) << 6) | (c3 & 63));
      } else {
        c2 = bytes[i++]; c3 = bytes[i++]; c4 = bytes[i++];
        c = ((c & 7) << 18) | ((c2 & 63) << 12) | ((c3 & 63) << 6) | (c4 & 63);
        c -= 0x10000;
        out += String.fromCharCode(0xd800 + (c >> 10), 0xdc00 + (c & 1023));
      }
    }
    return out;
  }

  function concat(parts) {
    var n = 0, i, off = 0, out;
    for (i = 0; i < parts.length; i++) n += parts[i].length;
    out = new Uint8Array(n);
    for (i = 0; i < parts.length; i++) { out.set(parts[i], off); off += parts[i].length; }
    return out;
  }

  function equalBytes(a, b) {
    if (a.length !== b.length) return false;
    var r = 0, i;
    for (i = 0; i < a.length; i++) r |= a[i] ^ b[i];
    return r === 0;
  }

  function u32be(v) {
    return new Uint8Array([(v >>> 24) & 255, (v >>> 16) & 255, (v >>> 8) & 255, v & 255]);
  }

  function randomBytes(n) {
    var out = new Uint8Array(n), i;
    try {
      if (typeof crypto !== "undefined" && crypto && crypto.getRandomValues) {
        crypto.getRandomValues(out);
        return out;
      }
    } catch (e) { /* fall through */ }
    for (i = 0; i < n; i++) out[i] = (Math.random() * 256) | 0;
    return out;
  }

  /* ------------------------------------------------------------ sha256 */

  var K256 = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
  ];

  function rotr(x, n) { return ((x >>> n) | (x << (32 - n))) >>> 0; }

  function sha256(msg) {
    var H = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];
    var len = msg.length;
    var padded = new Uint8Array(((len + 9 + 63) >> 6) << 6);
    padded.set(msg);
    padded[len] = 0x80;
    var dv = new DataView(padded.buffer);
    var bits = len * 8;
    dv.setUint32(padded.length - 8, Math.floor(bits / 4294967296));
    dv.setUint32(padded.length - 4, bits >>> 0);
    var W = new Uint32Array(64);
    var off, i, a, b, c, d, e, f, g, h, s0, s1, S1, ch, t1, S0, maj, t2;
    for (off = 0; off < padded.length; off += 64) {
      for (i = 0; i < 16; i++) W[i] = dv.getUint32(off + i * 4);
      for (i = 16; i < 64; i++) {
        s0 = rotr(W[i - 15], 7) ^ rotr(W[i - 15], 18) ^ (W[i - 15] >>> 3);
        s1 = rotr(W[i - 2], 17) ^ rotr(W[i - 2], 19) ^ (W[i - 2] >>> 10);
        W[i] = (W[i - 16] + s0 + W[i - 7] + s1) >>> 0;
      }
      a = H[0]; b = H[1]; c = H[2]; d = H[3]; e = H[4]; f = H[5]; g = H[6]; h = H[7];
      for (i = 0; i < 64; i++) {
        S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
        ch = (e & f) ^ (~e & g);
        t1 = (h + S1 + ch + K256[i] + W[i]) >>> 0;
        S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
        maj = (a & b) ^ (a & c) ^ (b & c);
        t2 = (S0 + maj) >>> 0;
        h = g; g = f; f = e; e = (d + t1) >>> 0; d = c; c = b; b = a; a = (t1 + t2) >>> 0;
      }
      H[0] = (H[0] + a) >>> 0; H[1] = (H[1] + b) >>> 0; H[2] = (H[2] + c) >>> 0; H[3] = (H[3] + d) >>> 0;
      H[4] = (H[4] + e) >>> 0; H[5] = (H[5] + f) >>> 0; H[6] = (H[6] + g) >>> 0; H[7] = (H[7] + h) >>> 0;
    }
    var out = new Uint8Array(32);
    var odv = new DataView(out.buffer);
    for (i = 0; i < 8; i++) odv.setUint32(i * 4, H[i]);
    return out;
  }

  function hmacSha256(key, msg) {
    if (key.length > 64) key = sha256(key);
    var k = new Uint8Array(64);
    k.set(key);
    var ipad = new Uint8Array(64), opad = new Uint8Array(64), i;
    for (i = 0; i < 64; i++) { ipad[i] = k[i] ^ 0x36; opad[i] = k[i] ^ 0x5c; }
    return sha256(concat([opad, sha256(concat([ipad, msg]))]));
  }

  function hkdf(ikm, salt, info, length) {
    var prk = hmacSha256(salt, ikm);
    var out = new Uint8Array(0), t = new Uint8Array(0), i = 1;
    while (out.length < length) {
      t = hmacSha256(prk, concat([t, info, new Uint8Array([i])]));
      out = concat([out, t]);
      i++;
    }
    return out.subarray(0, length);
  }

  /* --------------------------------------------------------------- AES */

  var SBOX = new Uint8Array([
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
  ]);

  function xtime(b) { return ((b << 1) ^ ((b & 0x80) ? 0x1b : 0)) & 255; }

  function aesExpandKey(key) {
    var Nk = 8, Nr = 14, Nw = 4 * (Nr + 1);
    var w = new Uint8Array(Nw * 4);
    w.set(key);
    var rcon = 1, i, t0, t1, t2, t3, tmp;
    for (i = Nk; i < Nw; i++) {
      t0 = w[(i - 1) * 4]; t1 = w[(i - 1) * 4 + 1]; t2 = w[(i - 1) * 4 + 2]; t3 = w[(i - 1) * 4 + 3];
      if (i % Nk === 0) {
        tmp = t0;
        t0 = SBOX[t1] ^ rcon; t1 = SBOX[t2]; t2 = SBOX[t3]; t3 = SBOX[tmp];
        rcon = xtime(rcon);
      } else if (i % Nk === 4) {
        t0 = SBOX[t0]; t1 = SBOX[t1]; t2 = SBOX[t2]; t3 = SBOX[t3];
      }
      w[i * 4] = w[(i - Nk) * 4] ^ t0;
      w[i * 4 + 1] = w[(i - Nk) * 4 + 1] ^ t1;
      w[i * 4 + 2] = w[(i - Nk) * 4 + 2] ^ t2;
      w[i * 4 + 3] = w[(i - Nk) * 4 + 3] ^ t3;
    }
    return w;
  }

  function aesEncryptBlock(rk, block) {
    var s = new Uint8Array(16), i, r, c, a0, a1, a2, a3, t16, row, col;
    for (i = 0; i < 16; i++) s[i] = block[i] ^ rk[i];
    for (r = 1; r <= 14; r++) {
      /* SubBytes + ShiftRows: state byte i = row + 4 * col */
      t16 = new Uint8Array(16);
      for (i = 0; i < 16; i++) {
        row = i & 3; col = i >> 2;
        t16[i] = SBOX[s[row + 4 * ((col + row) & 3)]];
      }
      s = t16;
      if (r !== 14) {
        for (c = 0; c < 4; c++) {
          a0 = s[c * 4]; a1 = s[c * 4 + 1]; a2 = s[c * 4 + 2]; a3 = s[c * 4 + 3];
          s[c * 4] = xtime(a0) ^ (xtime(a1) ^ a1) ^ a2 ^ a3;
          s[c * 4 + 1] = a0 ^ xtime(a1) ^ (xtime(a2) ^ a2) ^ a3;
          s[c * 4 + 2] = a0 ^ a1 ^ xtime(a2) ^ (xtime(a3) ^ a3);
          s[c * 4 + 3] = (xtime(a0) ^ a0) ^ a1 ^ a2 ^ xtime(a3);
        }
      }
      for (i = 0; i < 16; i++) s[i] ^= rk[r * 16 + i];
    }
    return s;
  }

  function inc32(counter) {
    var i = 15;
    while (i >= 12) {
      counter[i] = (counter[i] + 1) & 255;
      if (counter[i] !== 0) break;
      i--;
    }
  }

  function ghashMul(x, y) {
    var z = new Uint8Array(16), v = new Uint8Array(y), i, j, lsb;
    for (i = 0; i < 128; i++) {
      if ((x[i >> 3] >> (7 - (i & 7))) & 1) {
        for (j = 0; j < 16; j++) z[j] ^= v[j];
      }
      lsb = v[15] & 1;
      for (j = 15; j > 0; j--) v[j] = (v[j] >> 1) | ((v[j - 1] & 1) << 7);
      v[0] >>= 1;
      if (lsb) v[0] ^= 0xe1;
    }
    return z;
  }

  function ghash(H, aad, ct) {
    var y = new Uint8Array(16), i, pad;
    function absorb(block) {
      var k;
      for (k = 0; k < 16; k++) y[k] ^= block[k];
      y = ghashMul(y, H);
    }
    for (i = 0; i < aad.length; i += 16) {
      pad = new Uint8Array(16);
      pad.set(aad.subarray(i, Math.min(i + 16, aad.length)));
      absorb(pad);
    }
    for (i = 0; i < ct.length; i += 16) {
      pad = new Uint8Array(16);
      pad.set(ct.subarray(i, Math.min(i + 16, ct.length)));
      absorb(pad);
    }
    var lens = new Uint8Array(16);
    var dv = new DataView(lens.buffer);
    dv.setUint32(0, Math.floor((aad.length * 8) / 4294967296));
    dv.setUint32(4, (aad.length * 8) >>> 0);
    dv.setUint32(8, Math.floor((ct.length * 8) / 4294967296));
    dv.setUint32(12, (ct.length * 8) >>> 0);
    absorb(lens);
    return y;
  }

  function aesGcmEncrypt(key, nonce, plaintext, aad) {
    var rk = aesExpandKey(key);
    var H = aesEncryptBlock(rk, new Uint8Array(16));
    var j0 = new Uint8Array(16);
    j0.set(nonce);
    j0[15] = 1;
    var counter = new Uint8Array(j0);
    var ct = new Uint8Array(plaintext.length);
    var i, off, ks;
    for (off = 0; off < plaintext.length; off += 16) {
      inc32(counter);
      ks = aesEncryptBlock(rk, counter);
      for (i = 0; i < 16 && off + i < plaintext.length; i++) ct[off + i] = plaintext[off + i] ^ ks[i];
    }
    var tag = ghash(H, aad, ct);
    var e0 = aesEncryptBlock(rk, j0);
    for (i = 0; i < 16; i++) tag[i] ^= e0[i];
    return concat([ct, tag]);
  }

  function aesGcmDecrypt(key, nonce, ct, tag, aad) {
    var rk = aesExpandKey(key);
    var H = aesEncryptBlock(rk, new Uint8Array(16));
    var j0 = new Uint8Array(16);
    j0.set(nonce);
    j0[15] = 1;
    var counter = new Uint8Array(j0);
    var pt = new Uint8Array(ct.length);
    var i, off, ks;
    for (off = 0; off < ct.length; off += 16) {
      inc32(counter);
      ks = aesEncryptBlock(rk, counter);
      for (i = 0; i < 16 && off + i < ct.length; i++) pt[off + i] = ct[off + i] ^ ks[i];
    }
    var expect = ghash(H, aad, ct);
    var e0 = aesEncryptBlock(rk, j0);
    for (i = 0; i < 16; i++) expect[i] ^= e0[i];
    if (!equalBytes(expect, tag)) throw new Error("vidfast: invalid GCM tag");
    return pt;
  }

  /* ---------------------------------------------------------- base64 */

  var B64 = "", B64IDX = {};

  function rebuildAlphabet(alphabet62) {
    B64 = (alphabet62 || "") + "-_";
    B64IDX = {};
    for (var i = 0; i < B64.length; i++) B64IDX[B64.charAt(i)] = i;
  }

  function b64encode(data) {
    var out = "", acc = 0, nb = 0, i, b;
    for (i = 0; i < data.length; i++) {
      b = data[i];
      acc = (acc << 8) | b;
      nb += 8;
      while (nb >= 6) {
        nb -= 6;
        out += B64.charAt((acc >> nb) & 63);
      }
      acc &= (1 << nb) - 1;
    }
    if (nb) out += B64.charAt((acc << (6 - nb)) & 63);
    return out;
  }

  function b64decode(str) {
    var out = new Uint8Array(Math.floor((str.length * 6) / 8)), acc = 0, nb = 0, n = 0, i, v;
    for (i = 0; i < str.length; i++) {
      v = B64IDX[str.charAt(i)];
      if (v === undefined) throw new Error("vidfast: invalid base64 character");
      acc = (acc << 6) | v;
      nb += 6;
      if (nb >= 8) { nb -= 8; out[n++] = (acc >> nb) & 255; }
      acc &= (1 << nb) - 1;
    }
    return out.subarray(0, n);
  }

  /* ---------------------------------------------------- prng/permute */

  function prng(seedBytes) {
    var d = sha256(seedBytes);
    var dv = new DataView(d.buffer);
    var state = (dv.getUint32(0, true) ^ dv.getUint32(4, true) ^ dv.getUint32(8, true) ^ dv.getUint32(12, true)) >>> 0;
    return function () {
      var s = state;
      s ^= (s << 13) & 0xFFFFFFFF;
      s ^= s >>> 17;
      s ^= (s << 5) & 0xFFFFFFFF;
      s = s >>> 0;
      state = s;
      return s;
    };
  }

  function permutation(n, seedBytes) {
    var rnd = prng(seedBytes);
    var a = new Uint32Array(n), i, j, t;
    for (i = 0; i < n; i++) a[i] = i;
    for (i = n - 1; i > 0; i--) {
      j = rnd() % (i + 1);
      t = a[i]; a[i] = a[j]; a[j] = t;
    }
    return a;
  }

  function permute(input, idx) {
    var out = new Uint8Array(input.length), i;
    for (i = 0; i < input.length; i++) out[i] = input[idx[i]];
    return out;
  }

  function unpermute(input, idx) {
    var out = new Uint8Array(input.length), i;
    for (i = 0; i < input.length; i++) out[idx[i]] = input[i];
    return out;
  }

  function frameSeed(seed4, n) {
    return concat([utf8Encode("vidfast/v1/frame-permutation\u0000"), CFG.ikm_bytes, seed4, u32be(n)]);
  }

  /* ------------------------------------------------------------ frame */

  function tlv(type, value) {
    return concat([new Uint8Array([type]), u32be(value.length), value]);
  }

  function parseTlvs(blob) {
    var out = [], off = 0, t, len;
    while (off < blob.length) {
      if (off + 5 > blob.length) throw new Error("vidfast: truncated frame");
      t = blob[off];
      len = ((blob[off + 1] << 24) | (blob[off + 2] << 16) | (blob[off + 3] << 8) | blob[off + 4]) >>> 0;
      off += 5;
      if (off + len > blob.length) throw new Error("vidfast: invalid frame TLV");
      out.push({ type: t, value: blob.subarray(off, off + len) });
      off += len;
    }
    return out;
  }

  var KIND = { request: 1, servers: 2, stream: 3 };

  function aesKey(keyInfo, salt) {
    var info = concat([utf8Encode("vidfast/v1/aes-256-gcm\u0000"), sha256(keyInfo)]);
    return hkdf(CFG.ikm_bytes, salt, info, 32);
  }

  function encodeFrame(plaintext, kind) {
    var salt = randomBytes(16), nonce = randomBytes(12), seed4 = randomBytes(4);
    var head = concat([
      tlv(1, utf8Encode("VF1")), tlv(2, new Uint8Array([1])), tlv(3, new Uint8Array([1])),
      tlv(4, utf8Encode(CFG.buildId)), tlv(5, new Uint8Array([KIND[kind]])), tlv(6, u32be(plaintext.length))
    ]);
    var ctTag = aesGcmEncrypt(aesKey(head, salt), nonce, plaintext, head);
    var ct = ctTag.subarray(0, ctTag.length - 16);
    var tag = ctTag.subarray(ctTag.length - 16);
    var blob = concat([head, tlv(7, salt), tlv(8, nonce), tlv(9, ct), tlv(10, tag)]);
    var idx = permutation(blob.length, frameSeed(seed4, blob.length));
    return b64encode(concat([seed4, permute(blob, idx)]));
  }

  function decodeFrame(wire, expectedKind) {
    var raw = b64decode(wire);
    if (raw.length < 8) throw new Error("vidfast: frame too short");
    var seed4 = raw.subarray(0, 4), body = raw.subarray(4);
    var idx = permutation(body.length, frameSeed(seed4, body.length));
    var blob = unpermute(body, idx);
    var tls = parseTlvs(blob);
    var map = {}, i;
    for (i = 0; i < tls.length; i++) map[tls[i].type] = tls[i].value;
    if (!map[1] || utf8Decode(map[1]) !== "VF1") throw new Error("vidfast: invalid frame magic");
    if (map[2][0] !== 1 || map[3][0] !== 1) throw new Error("vidfast: unsupported frame version");
    if (utf8Decode(map[4]) !== CFG.buildId) throw new Error("vidfast: protection build changed");
    if (expectedKind && map[5][0] !== KIND[expectedKind]) throw new Error("vidfast: unexpected frame kind");
    var tail = 4 * 5 + map[7].length + map[8].length + map[9].length + map[10].length;
    var head = blob.subarray(0, blob.length - tail);
    var pt = aesGcmDecrypt(aesKey(head, map[7]), map[8], map[9], map[10], head);
    var declared = ((map[6][0] << 24) | (map[6][1] << 16) | (map[6][2] << 8) | map[6][3]) >>> 0;
    if (pt.length !== declared) throw new Error("vidfast: frame length mismatch");
    return { kind: map[5][0], plaintext: pt };
  }

  /* ---------------------------------------------------- outer ticket */

  function outerSeed(seed4, label, length) {
    return concat([utf8Encode("vidfast/v1/" + label + "\u0000"), CFG.ikm_bytes, seed4, u32be(length)]);
  }

  function rotl8(v, a) {
    a &= 7;
    return a ? (((v << a) | (v >>> (8 - a))) & 255) : v;
  }

  function encodeOuterTicket(ticket, seed4) {
    seed4 = seed4 || randomBytes(4);
    var data = typeof ticket === "string" ? utf8Encode(ticket) : ticket;
    var n = data.length;
    if (!n || n > 16384) throw new Error("vidfast: invalid ticket");
    var rnd = prng(outerSeed(seed4, "outer-transform", n));
    var tr = new Uint8Array(n), i, xor, rot, add;
    for (i = 0; i < n; i++) {
      xor = rnd() & 255;
      rot = (rnd() % 7) + 1;
      add = (rnd() + Math.imul(i, 17)) & 255;
      tr[i] = (rotl8(data[i] ^ xor, rot) + add) & 255;
    }
    var idx = permutation(n, outerSeed(seed4, "outer-permutation", n));
    return b64encode(concat([seed4, permute(tr, idx)]));
  }

  /* ----------------------------------------------------------- config */

  function configure(cfg) {
    CFG.prefix = cfg.prefix;
    CFG.buildId = cfg.buildId;
    CFG.alphabet62 = cfg.alphabet62;
    CFG.ikm = cfg.ikm;
    CFG.endpoints = cfg.endpoints || CFG.endpoints;
    CFG.ikm_bytes = hexToBytes(cfg.ikm);
    rebuildAlphabet(cfg.alphabet62);
  }

  configure(VIDFAST_STATIC_CONFIG);

  return {
    configure: configure,
    config: function () {
      return {
        prefix: CFG.prefix, buildId: CFG.buildId, alphabet62: CFG.alphabet62,
        ikm: CFG.ikm, endpoints: CFG.endpoints
      };
    },
    utf8Encode: utf8Encode, utf8Decode: utf8Decode,
    sha256: sha256, hmacSha256: hmacSha256, hkdf: hkdf,
    aesGcmEncrypt: aesGcmEncrypt, aesGcmDecrypt: aesGcmDecrypt,
    b64encode: b64encode, b64decode: b64decode,
    encodeFrame: encodeFrame, decodeFrame: decodeFrame,
    encodeOuterTicket: encodeOuterTicket,
    hexToBytes: hexToBytes, bytesToHex: bytesToHex, concat: concat
  };
})();

/* ==========================================================================
 * 2. HTTP helpers
 * ========================================================================== */

function vfLog(message) {
  try { console.log("[vidfast] " + message); } catch (error) { /* ignore */ }
}

async function vidfastRequest(url, headers, method, body) {
  var verb = method || "GET";

  if (typeof fetchv2 === "function") {
    var response = await fetchv2(url, headers || {}, verb, body == null ? null : body, true);
    if (response == null) throw new Error(verb + " " + url + " returned nothing");
    var status = typeof response.status === "number" ? response.status : 200;
    var text;
    if (response._data != null) text = String(response._data);
    else if (typeof response.text === "function") text = String(await response.text());
    else if (typeof response.text === "string") text = response.text;
    else text = String(response);
    return { status: status, text: text };
  }

  /* Very old Sora builds only expose fetch(). */
  if (typeof fetch === "function") {
    if (verb !== "GET") throw new Error("POST needs fetchv2, which this Sora build does not provide");
    var legacy = await fetch(url, headers || {});
    return { status: 200, text: legacy == null ? "" : String(legacy) };
  }

  throw new Error("no fetch implementation available");
}

function vidfastHeaders(extra) {
  var headers = { "User-Agent": VIDFAST_UA, "Referer": VIDFAST_REFERER };
  var key;
  for (key in extra) {
    if (Object.prototype.hasOwnProperty.call(extra, key)) headers[key] = extra[key];
  }
  return headers;
}

/* ==========================================================================
 * 3. Protection config discovery (used when the baked-in config is stale)
 * ========================================================================== */

function vfCanonicalJson(value) {
  if (value === null || typeof value !== "object") return JSON.stringify(value);
  var i, keys, parts;
  if (Object.prototype.toString.call(value) === "[object Array]") {
    parts = [];
    for (i = 0; i < value.length; i++) parts.push(vfCanonicalJson(value[i]));
    return "[" + parts.join(",") + "]";
  }
  keys = Object.keys(value).sort();
  parts = [];
  for (i = 0; i < keys.length; i++) parts.push(JSON.stringify(keys[i]) + ":" + vfCanonicalJson(value[keys[i]]));
  return "{" + parts.join(",") + "}";
}

async function vidfastDiscoverConfig(html) {
  var pageChunkPath = /src="(\/_next\/static\/chunks\/[^"]*page-[0-9a-f]+\.js)"/.exec(html || "");
  var runtimePath = /src="(\/_next\/static\/chunks\/webpack-[^"]+\.js)"/.exec(html || "");
  if (!pageChunkPath || !runtimePath) throw new Error("vidfast: cannot locate bundle chunks");

  var runtime = (await vidfastRequest(VIDFAST_ORIGIN + runtimePath[1], vidfastHeaders({}))).text;
  var mapStart = runtime.indexOf("r.u=");
  var mapEnd = runtime.indexOf("r.miniCssF", mapStart);
  var mapText = runtime.slice(mapStart, mapEnd > 0 ? mapEnd : mapStart + 4000);
  var hashes = {}, pair, pairRe = /(\d+):"([0-9a-f]{8,})"/g;
  while ((pair = pairRe.exec(mapText))) hashes[pair[1]] = pair[2];

  var pageChunk = (await vidfastRequest(VIDFAST_ORIGIN + pageChunkPath[1], vidfastHeaders({}))).text;
  var anchor = pageChunk.indexOf('playerVariant=1"');
  if (anchor < 0) throw new Error("vidfast: player variant 1 not found");
  var listStart = pageChunk.lastIndexOf("Promise.all([", anchor);
  if (listStart < 0) throw new Error("vidfast: player chunk list not found");
  var listEnd = pageChunk.indexOf("])", listStart);
  var ids = (pageChunk.slice(listStart, listEnd + 2).match(/\d+/g) || []);
  if (!ids.length) throw new Error("vidfast: player chunk id not found");

  var chunkText = null, i, id, url, res;
  for (i = ids.length - 1; i >= 0 && chunkText === null; i--) {
    id = ids[i];
    if (!hashes[id] || hashes[id].length < 12) continue;
    url = VIDFAST_ORIGIN + "/_next/static/chunks/" + id + "." + hashes[id] + ".js";
    res = await vidfastRequest(url, vidfastHeaders({}));
    if (res.status === 200 && res.text.indexOf("_v1BuildId") >= 0) chunkText = res.text;
  }
  if (chunkText === null) throw new Error("vidfast: protection chunk not found");

  var prefix = /"(\/APA91cut[^"]{150,260})"/.exec(chunkText);
  var build = /"([A-Za-z0-9_-]{40,60})","_v1BuildId"/.exec(chunkText);
  var alpha = /"([A-Za-z0-9]{40,90})","_v1Alphabet"/.exec(chunkText);
  var manifest = /"parse",'(\{[^']*\})'/.exec(chunkText);
  if (!prefix || !build || !alpha || !manifest) throw new Error("vidfast: protection config incomplete");

  var manifestText = vfCanonicalJson(JSON.parse(manifest[1]));
  var keyInfo = VF.utf8Encode("vidfast/protection/variant-1/public\u0000" + build[1] + "\u0000" + manifestText);
  var ikm = VF.bytesToHex(VF.sha256(keyInfo));

  var cfg = {
    prefix: prefix[1],
    buildId: build[1],
    alphabet62: alpha[1],
    ikm: ikm,
    endpoints: VF.config().endpoints
  };
  VF.configure(cfg);
  vfLog("protection config refreshed (build " + cfg.buildId.slice(0, 8) + ")");
  return cfg;
}

/* ==========================================================================
 * 4. vidfast stream resolution
 * ========================================================================== */

function vidfastFindToken(html) {
  var m = /\\?"en\\?":\\?"([A-Za-z0-9_-]{60,300})/.exec(html || "");
  if (m) return m[1];
  m = /"en":"([A-Za-z0-9_-]{60,300})"/.exec(html || "");
  return m ? m[1] : null;
}

function vidfastApiUrl(pathPart) {
  var cfg = VF.config();
  return VIDFAST_ORIGIN + cfg.prefix + "/" + cfg.endpoints[pathPart] + "/";
}

async function vidfastPost(pathPart, payload) {
  return vidfastRequest(vidfastApiUrl(pathPart) + payload, vidfastHeaders({}), "POST");
}

async function vidfastResolveStreams(pageUrl) {
  var page = await vidfastRequest(pageUrl, vidfastHeaders({}));
  if (page.status !== 200) throw new Error("vidfast: page " + page.status);
  var token = vidfastFindToken(page.text);
  if (!token) throw new Error("vidfast: no player token on page");

  var refreshed = false;
  for (var attempt = 0; attempt < 2; attempt++) {
    var boot = await vidfastPost("bootstrap", VF.encodeFrame(VF.utf8Encode(token), "request"));
    if (boot.status === 200 && boot.text.length > 20) {
      var servers = await vidfastPost("servers", VF.encodeOuterTicket(boot.text));
      if (servers.status === 200) {
        var list = JSON.parse(VF.utf8Decode(VF.decodeFrame(servers.text, "servers").plaintext));
        return await vidfastCollectStreams(list);
      }
      vfLog("servers endpoint: HTTP " + servers.status);
    } else {
      vfLog("bootstrap endpoint: HTTP " + boot.status);
    }
    if (refreshed) break;
    refreshed = true;
    await vidfastDiscoverConfig(page.text);
    token = vidfastFindToken(page.text) || token;
  }
  throw new Error("vidfast: could not open a stream session");
}

var VIDFAST_KIND_ORDER = ["vRapid", "vBlaze", "Cobra", "Bravo", "Delta"];

function vidfastServerRank(name) {
  var i = VIDFAST_KIND_ORDER.indexOf(name);
  return i < 0 ? 99 : i;
}

async function vidfastCollectStreams(servers) {
  if (!servers || !servers.length) throw new Error("vidfast: empty server list");

  var ordered = servers.slice().sort(function (a, b) {
    return vidfastServerRank(String(a.name)) - vidfastServerRank(String(b.name));
  });

  var streams = [];
  for (var i = 0; i < ordered.length; i++) {
    var server = ordered[i];
    if (!server || !server.data) continue;
    var res = await vidfastPost("stream", server.data);
    if (res.status === 429 || res.status === 403) {
      vfLog("rate limited by vidfast, stopping after " + streams.length + " server(s)");
      break;
    }
    if (res.status !== 200) {
      vfLog("server " + server.name + " failed with HTTP " + res.status);
      continue;
    }
    try {
      var info = JSON.parse(VF.utf8Decode(VF.decodeFrame(res.text, "stream").plaintext));
      if (!info || !info.url) continue;
      var label = String(server.name || "Server");
      if (server.description) label += " \u00b7 " + server.description;
      var headers = {};
      if (!info.noReferrer) {
        headers["Referer"] = VIDFAST_REFERER;
        headers["User-Agent"] = VIDFAST_UA;
      }
      streams.push({ streamUrl: String(info.url), title: label, headers: headers });
    } catch (error) {
      vfLog("server " + server.name + " decode failed: " + error);
    }
  }

  if (!streams.length) throw new Error("vidfast: no playable server answered");
  return streams;
}


/* Like vidfastRequest, but returns null instead of throwing (metadata only). */
async function vidfastTryRequest(url, headers) {
  try { return await vidfastRequest(url, headers); }
  catch (error) { return null; }
}

/* ==========================================================================
 * 5. Metadata helpers
 * ========================================================================== */

function vidfastStripHtml(text) {
  if (!text) return "";
  var out = String(text).replace(/<br\s*\/?>/gi, " ").replace(/<[^>]+>/g, "");
  out = out.replace(/&nbsp;/g, " ").replace(/&amp;/g, "&").replace(/&quot;/g, '"')
    .replace(/&#39;/g, "'").replace(/&lt;/g, "<").replace(/&gt;/g, ">");
  return out.replace(/\s+/g, " ").trim();
}

function vidfastYear(date) {
  return date ? String(date).slice(0, 4) : "";
}

async function vidfastImdbSuggest(query) {
  var url = "https://v3.sg.media-imdb.com/suggestion/x/" + encodeURIComponent(query) + ".json";
  var res = await vidfastTryRequest(url, vidfastHeaders({ "Accept": "application/json" }));
  if (!res || res.status !== 200) return [];
  try {
    var data = JSON.parse(res.text);
    return data && data.d ? data.d : [];
  } catch (error) {
    return [];
  }
}

async function vidfastTvmazeLookup(imdbId) {
  if (!imdbId) return null;
  var url = "https://api.tvmaze.com/lookup/shows?imdb=" + encodeURIComponent(imdbId);
  var res = await vidfastTryRequest(url, { "User-Agent": VIDFAST_META_UA, "Accept": "application/json" });
  if (!res || res.status !== 200) return null;
  try { return JSON.parse(res.text); } catch (error) { return null; }
}

async function vidfastTvmazeEpisodes(showId) {
  var url = "https://api.tvmaze.com/shows/" + encodeURIComponent(String(showId)) + "/episodes";
  var res = await vidfastTryRequest(url, { "User-Agent": VIDFAST_META_UA, "Accept": "application/json" });
  if (!res || res.status !== 200) return [];
  try {
    var data = JSON.parse(res.text);
    return data && data.length ? data : [];
  } catch (error) {
    return [];
  }
}

async function vidfastTvmazeSearch(query) {
  var url = "https://api.tvmaze.com/search/shows?q=" + encodeURIComponent(query);
  var res = await vidfastTryRequest(url, { "User-Agent": VIDFAST_META_UA, "Accept": "application/json" });
  if (!res || res.status !== 200) return [];
  try {
    var data = JSON.parse(res.text);
    return data && data.length ? data : [];
  } catch (error) {
    return [];
  }
}

async function vidfastWikiIntro(query) {
  var url = "https://en.wikipedia.org/w/api.php?action=query&format=json&formatversion=2" +
    "&generator=search&gsrlimit=1&prop=extracts&exintro=1&explaintext=1&gsrsearch=" +
    encodeURIComponent(query);
  var res = await vidfastTryRequest(url, { "User-Agent": VIDFAST_META_UA, "Accept": "application/json" });
  if (!res || res.status !== 200) return "";
  try {
    var data = JSON.parse(res.text);
    var pages = (data && data.query && data.query.pages) || [];
    if (!pages.length) return "";
    return vidfastStripHtml(pages[0].extract || "");
  } catch (error) {
    return "";
  }
}

/* REST summary is the CORS-friendly fallback when the action API is blocked. */
async function vidfastWikiSummary(title) {
  if (!title) return "";
  var url = "https://en.wikipedia.org/api/rest_v1/page/summary/" +
    encodeURIComponent(String(title).replace(/ /g, "_"));
  var res = await vidfastTryRequest(url, { "User-Agent": VIDFAST_META_UA, "Accept": "application/json" });
  if (!res || res.status !== 200) return "";
  try {
    var data = JSON.parse(res.text);
    if (!data || data.type === "disambiguation") return "";
    return vidfastStripHtml(data.extract || "");
  } catch (error) {
    return "";
  }
}

/* ==========================================================================
 * 6. URL helpers
 * ========================================================================== */

function vidfastParseUrl(url) {
  var text = String(url || "");
  var tmdb = /\/tv\/(\d+)\/(\d+)\/(\d+)/.exec(text);
  var imdbTv = /\/tv\/(tt\d+)(?:\/(\d+)\/(\d+))?/.exec(text);
  var imdbMovie = /\/movie\/(tt\d+)/.exec(text);
  var tmdbMovie = /\/movie\/(\d+)/.exec(text);

  if (imdbTv) {
    return {
      kind: "tv", id: imdbTv[1], isImdb: true,
      season: imdbTv[2] ? parseInt(imdbTv[2], 10) : 1,
      episode: imdbTv[3] ? parseInt(imdbTv[3], 10) : 1
    };
  }
  if (imdbMovie) return { kind: "movie", id: imdbMovie[1], isImdb: true };
  if (tmdb) {
    return {
      kind: "tv", id: tmdb[1], isImdb: false,
      season: parseInt(tmdb[2], 10), episode: parseInt(tmdb[3], 10)
    };
  }
  if (tmdbMovie) return { kind: "movie", id: tmdbMovie[1], isImdb: false };
  return null;
}

function vidfastEpisodeUrl(id, season, episode) {
  return VIDFAST_ORIGIN + "/tv/" + id + "/" + season + "/" + episode;
}

function vidfastMovieUrl(id) {
  return VIDFAST_ORIGIN + "/movie/" + id;
}

/* ==========================================================================
 * 7. Sora entry points
 * ========================================================================== */

async function searchResults(keyword) {
  var query = String(keyword || "").trim();
  if (!query) return JSON.stringify([]);

  var results = [];
  var seen = {};

  function push(item) {
    if (!item || seen[item.href]) return;
    seen[item.href] = true;
    results.push(item);
  }

  try {
    var suggestions = await vidfastImdbSuggest(query);
    for (var i = 0; i < suggestions.length && results.length < 12; i++) {
      var s = suggestions[i] || {};
      var id = String(s.id || "");
      if (!/^tt\d{5,}$/.test(id)) continue;

      var type = String(s.q || "").toLowerCase();
      if (type.indexOf("episode") >= 0) continue;
      if (type.indexOf("game") >= 0) continue;
      if (type.indexOf("podcast") >= 0) continue;
      if (type.indexOf("music") >= 0) continue;
      if (type.indexOf("short") >= 0) continue;

      var isSeries = type.indexOf("series") >= 0;
      var year = s.y ? String(s.y) : "";
      var title = String(s.l || id);
      if (year) title += " (" + year + ")";

      push({
        title: title,
        image: (s.i && s.i.imageUrl) ? String(s.i.imageUrl) : "",
        href: isSeries ? VIDFAST_ORIGIN + "/tv/" + id : vidfastMovieUrl(id)
      });
    }
  } catch (error) {
    vfLog("imdb search failed: " + error);
  }

  if (!results.length) {
    try {
      var shows = await vidfastTvmazeSearch(query);
      for (var j = 0; j < shows.length && results.length < 12; j++) {
        var show = (shows[j] || {}).show || {};
        var imdb = (show.externals || {}).imdb;
        if (!imdb) continue;
        var label = String(show.name || "");
        var premiered = vidfastYear(show.premiered);
        if (premiered) label += " (" + premiered + ")";
        push({
          title: label,
          image: (show.image && (show.image.medium || show.image.original)) || "",
          href: VIDFAST_ORIGIN + "/tv/" + imdb
        });
      }
    } catch (error) {
      vfLog("tvmaze search failed: " + error);
    }
  }

  return JSON.stringify(results);
}

async function extractDetails(url) {
  var parsed = vidfastParseUrl(url);
  var description = "";
  var aliases = "";
  var airdate = "";

  if (parsed && parsed.kind === "tv" && parsed.isImdb) {
    var show = await vidfastTvmazeLookup(parsed.id);
    if (show) {
      description = vidfastStripHtml(show.summary);
      aliases = (show.genres || []).join(", ");
      var network = show.network || show.webChannel;
      if (network && network.name) aliases += (aliases ? " \u00b7 " : "") + network.name;
      var start = vidfastYear(show.premiered);
      var end = vidfastYear(show.ended);
      airdate = start ? (end && end !== start ? start + "\u2013" + end : start + "\u2013present") : "";
    }
  } else if (parsed && parsed.kind === "movie") {
    var title = "";
    var year = "";
    if (parsed.isImdb) {
      var hits = await vidfastImdbSuggest(parsed.id);
      if (hits && hits.length) {
        title = String(hits[0].l || "");
        year = hits[0].y ? String(hits[0].y) : "";
      }
    }
    aliases = "Movie" + (year ? " \u00b7 " + year : "");
    airdate = year;
    if (title) {
      description = await vidfastWikiIntro(title + (year ? " " + year : "") + " film");
      if (!description) description = await vidfastWikiSummary(title + (year ? " (" + year + " film)" : ""));
      if (!description) description = await vidfastWikiSummary(title);
      if (!description) description = title + (year ? " (" + year + ")" : "") + " \u2014 movie available on vidfast.";
    }
  } else if (!parsed) {
    airdate = "";
  }

  if (!description) description = "Available on vidfast.";
  if (!aliases) aliases = "vidfast";

  return JSON.stringify([{ description: description, aliases: aliases, airdate: airdate }]);
}

async function extractEpisodes(url) {
  var parsed = vidfastParseUrl(url);
  if (!parsed) return JSON.stringify([]);

  /* Movies: Sora hides the episode list when exactly one entry is returned. */
  if (parsed.kind === "movie") {
    return JSON.stringify([{ number: 1, href: vidfastMovieUrl(parsed.id) }]);
  }

  if (!parsed.isImdb) {
    /* A TMDB id cannot be mapped to TVMaze without a TMDB key, so fall back to
       a single "episode" (Sora then plays the URL like a movie). */
    return JSON.stringify([{ number: 1, href: vidfastEpisodeUrl(parsed.id, parsed.season, parsed.episode) }]);
  }

  var show = await vidfastTvmazeLookup(parsed.id);
  if (!show || !show.id) {
    return JSON.stringify([{ number: 1, href: vidfastEpisodeUrl(parsed.id, parsed.season, parsed.episode) }]);
  }

  var episodes = await vidfastTvmazeEpisodes(show.id);
  var list = [];
  for (var i = 0; i < episodes.length; i++) {
    var ep = episodes[i] || {};
    var season = parseInt(ep.season, 10);
    var number = parseInt(ep.number, 10);
    if (!season || !number || season <= 0) continue;
    /* Sora starts a new season whenever `number` decreases, so the number is
       kept inside the season (1..N) and repeated for every season. */
    list.push({
      number: number,
      season: season,
      href: vidfastEpisodeUrl(parsed.id, season, number)
    });
  }

  list.sort(function (a, b) {
    return a.season === b.season ? a.number - b.number : a.season - b.season;
  });

  if (!list.length) {
    return JSON.stringify([{ number: 1, href: vidfastEpisodeUrl(parsed.id, parsed.season, parsed.episode) }]);
  }

  var result = [];
  for (var j = 0; j < list.length; j++) {
    result.push({ number: list[j].number, href: list[j].href });
  }
  return JSON.stringify(result);
}

async function extractStreamUrl(url) {
  var parsed = vidfastParseUrl(url);
  if (!parsed) throw new Error("vidfast: cannot parse URL " + url);

  var pageUrl;
  if (parsed.kind === "movie") pageUrl = vidfastMovieUrl(parsed.id);
  else pageUrl = vidfastEpisodeUrl(parsed.id, parsed.season, parsed.episode);

  var streams = await vidfastResolveStreams(pageUrl);
  return JSON.stringify({ streams: streams });
}
