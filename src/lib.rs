//! A small, self-contained SHA1 and HMAC-SHA1 implementation
//! (C) Frank Denis <fdenis [at] fastly [dot] com>, public domain

#![no_std]
#![allow(
    non_snake_case,
    clippy::cast_lossless,
    clippy::eq_op,
    clippy::identity_op,
    clippy::many_single_char_names,
    clippy::unreadable_literal
)]

#[inline(always)]
fn load_be(base: &[u8], offset: usize) -> u32 {
    let addr = &base[offset..];
    (addr[3] as u32) | (addr[2] as u32) << 8 | (addr[1] as u32) << 16 | (addr[0] as u32) << 24
}

#[inline(always)]
fn store_be(base: &mut [u8], offset: usize, x: u32) {
    let addr = &mut base[offset..];
    addr[3] = x as u8;
    addr[2] = (x >> 8) as u8;
    addr[1] = (x >> 16) as u8;
    addr[0] = (x >> 24) as u8;
}

#[derive(Copy, Clone)]
struct State([u32; 5]);

impl State {
    fn new() -> Self {
        State([0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0])
    }

    fn store(&self, out: &mut [u8]) {
        for (i, &e) in self.0.iter().enumerate() {
            store_be(out, i * 4, e);
        }
    }

    fn blocks(&mut self, mut input: &[u8]) -> usize {
        let mut inlen = input.len();
        let mut w = [0u32; 80];
        while inlen >= 64 {
            for i in 0..16 {
                w[i] = load_be(input, i * 4);
            }
            for i in 16..80 {
                w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
            }
            let mut t = self.0;

            for (i, wi) in w.iter().enumerate() {
                let (f, k) = match i {
                    0..=19 => (t[1] & t[2] | !t[1] & t[3], 0x5a827999),
                    20..=39 => (t[1] ^ t[2] ^ t[3], 0x6ed9eba1),
                    40..=59 => (t[1] & t[2] | t[1] & t[3] | t[2] & t[3], 0x8f1bbcdc),
                    60..=79 => (t[1] ^ t[2] ^ t[3], 0xca62c1d6),
                    _ => unreachable!(),
                };
                let g = t[0]
                    .rotate_left(5)
                    .wrapping_add(f.wrapping_add(t[4].wrapping_add(wi.wrapping_add(k))));
                t[4] = t[3];
                t[3] = t[2];
                t[2] = t[1].rotate_left(30);
                t[1] = t[0];
                t[0] = g;
            }
            for (i, s) in self.0.iter_mut().enumerate() {
                *s = s.wrapping_add(t[i]);
            }
            input = &input[64..];
            inlen -= 64;
        }
        inlen
    }
}

#[derive(Copy, Clone)]
pub struct Hash {
    state: State,
    w: [u8; 64],
    r: usize,
    len: usize,
}

impl Hash {
    pub fn new() -> Hash {
        Hash {
            state: State::new(),
            r: 0,
            w: [0u8; 64],
            len: 0,
        }
    }

    fn _update<T: AsRef<[u8]>>(&mut self, input: T) {
        let input = input.as_ref();
        let mut n = input.len();
        self.len += n;
        let av = 64 - self.r;
        let tc = ::core::cmp::min(n, av);
        self.w[self.r..self.r + tc].copy_from_slice(&input[0..tc]);
        self.r += tc;
        n -= tc;
        let pos = tc;
        if self.r == 64 {
            self.state.blocks(&self.w);
            self.r = 0;
        }
        if self.r == 0 && n > 0 {
            let rb = self.state.blocks(&input[pos..]);
            if rb > 0 {
                self.w[..rb].copy_from_slice(&input[pos + n - rb..]);
                self.r = rb;
            }
        }
    }

    /// Absorb content
    pub fn update<T: AsRef<[u8]>>(&mut self, input: T) {
        self._update(input)
    }

    /// Compute SHA1(absorbed content)
    pub fn finalize(mut self) -> [u8; 20] {
        let mut padded = [0u8; 128];
        padded[..self.r].copy_from_slice(&self.w[..self.r]);
        padded[self.r] = 0x80;
        let r = if self.r < 56 { 64 } else { 128 };
        let bits = self.len * 8;
        for i in 0..8 {
            padded[r - 8 + i] = (bits as u64 >> (56 - i * 8)) as u8;
        }
        self.state.blocks(&padded[..r]);
        let mut out = [0u8; 20];
        self.state.store(&mut out);
        out
    }

    /// Compute SHA1(`input`)
    pub fn hash(input: &[u8]) -> [u8; 20] {
        let mut h = Hash::new();
        h.update(input);
        h.finalize()
    }
}

impl Default for Hash {
    fn default() -> Self {
        Self::new()
    }
}

pub struct HMAC;

impl HMAC {
    /// Compute HMAC-SHA1(`input`, `k`)
    pub fn mac(input: &[u8], k: &[u8]) -> [u8; 20] {
        let mut hk = [0u8; 20];
        let k2 = if k.len() > 64 {
            hk.copy_from_slice(&Hash::hash(k));
            &hk
        } else {
            k
        };
        let mut padded = [0x36; 40];
        for (p, &k) in padded.iter_mut().zip(k2.iter()) {
            *p ^= k;
        }
        let mut ih = Hash::new();
        ih.update(&padded[..]);
        ih.update(input);

        for p in padded.iter_mut() {
            *p ^= 0x6a;
        }
        let mut oh = Hash::new();
        oh.update(&padded[..]);
        oh.update(ih.finalize());
        oh.finalize()
    }
}

#[cfg(feature = "traits09")]
mod digest_trait09 {
    use digest09::consts::{U32, U64};
    use digest09::{BlockInput, FixedOutputDirty, Output, Reset, Update};

    use super::Hash;

    impl BlockInput for Hash {
        type BlockSize = U64;
    }

    impl Update for Hash {
        fn update(&mut self, input: impl AsRef<[u8]>) {
            self._update(input)
        }
    }

    impl FixedOutputDirty for Hash {
        type OutputSize = U32;

        fn finalize_into_dirty(&mut self, out: &mut Output<Self>) {
            let h = self.finalize();
            out.copy_from_slice(&h);
        }
    }

    impl Reset for Hash {
        fn reset(&mut self) {
            *self = Self::new()
        }
    }
}

/// Wrapped `Hash` type for the `Digest` trait.
#[cfg(feature = "traits010")]
pub type WrappedHash = digest010::core_api::CoreWrapper<Hash>;

#[cfg(feature = "traits010")]
mod digest_trait010 {
    use core::fmt;

    use digest010::{
        block_buffer::Eager,
        const_oid::{AssociatedOid, ObjectIdentifier},
        consts::{U20, U64},
        core_api::{
            AlgorithmName, Block, BlockSizeUser, Buffer, BufferKindUser, FixedOutputCore,
            OutputSizeUser, Reset, UpdateCore,
        },
        HashMarker,
    };

    use super::Hash;

    impl AssociatedOid for Hash {
        const OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.14.3.2.26");
    }

    impl AlgorithmName for Hash {
        fn write_alg_name(f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("Sha1")
        }
    }

    impl HashMarker for Hash {}

    impl BufferKindUser for Hash {
        type BufferKind = Eager;
    }

    impl BlockSizeUser for Hash {
        type BlockSize = U64;
    }

    impl OutputSizeUser for Hash {
        type OutputSize = U20;
    }

    impl UpdateCore for Hash {
        #[inline]
        fn update_blocks(&mut self, blocks: &[Block<Self>]) {
            for block in blocks {
                self._update(block)
            }
        }
    }

    impl FixedOutputCore for Hash {
        fn finalize_fixed_core(
            &mut self,
            buffer: &mut Buffer<Self>,
            out: &mut digest010::Output<Self>,
        ) {
            self._update(buffer.get_data());
            let h = self.finalize();
            out.copy_from_slice(&h);
        }
    }

    impl Reset for Hash {
        fn reset(&mut self) {
            *self = Self::new()
        }
    }
}

#[test]
fn main() {
    let h = Hash::hash(b"");
    assert_eq!(
        &h[..],
        &[218, 57, 163, 238, 94, 107, 75, 13, 50, 85, 191, 239, 149, 96, 24, 144, 175, 216, 7, 9]
    );

    let h = Hash::hash(b"test");
    assert_eq!(
        &h[..],
        &[
            169, 74, 143, 229, 204, 177, 155, 166, 28, 76, 8, 115, 211, 145, 233, 135, 152, 47,
            187, 211
        ]
    );

    let h = Hash::hash(b"XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX");
    assert_eq!(
        &h[..],
        &[
            83, 198, 188, 169, 11, 131, 194, 106, 152, 41, 132, 130, 87, 94, 225, 72, 154, 232, 71,
            164
        ]
    );

    let h = HMAC::mac(&[42u8; 69], &[]);
    assert_eq!(
        &h[..],
        &[
            145, 126, 228, 73, 171, 107, 124, 27, 28, 215, 16, 100, 14, 136, 213, 49, 251, 121,
            205, 27
        ]
    );

    let h = HMAC::mac(&[69u8; 250], &[42u8; 50]);
    assert_eq!(
        &h[..],
        &[44, 56, 48, 37, 170, 240, 168, 220, 81, 38, 5, 248, 34, 189, 41, 26, 218, 93, 126, 133]
    );
}

#[cfg(feature = "traits010")]
#[test]
fn main_traits() {
    use digest010::Digest;
    let mut h = WrappedHash::new();
    Digest::update(&mut h, b"");
    assert_eq!(
        h.finalize().as_slice(),
        &[218, 57, 163, 238, 94, 107, 75, 13, 50, 85, 191, 239, 149, 96, 24, 144, 175, 216, 7, 9]
    );

    let mut h = WrappedHash::new();
    Digest::update(&mut h, b"test");
    assert_eq!(
        h.finalize().as_slice(),
        &[
            169, 74, 143, 229, 204, 177, 155, 166, 28, 76, 8, 115, 211, 145, 233, 135, 152, 47,
            187, 211
        ]
    );
}
