#![no_std]

/// A single bit of a bitmask filter.
///
/// A Set bit will match only a set bit, a Reset bit will match only a reset bit, and Any
/// will match any bit value.
///
/// The EXACT const generic determines the interpretation of the mask bit. A true value means
/// that set bits in the mask match the value exactly. A false value means that reset
/// bits in the mask match exactly.
///
#[derive(Debug, Clone, Copy)]
pub enum Selector<const EXACT: bool> {
    Set,
    Reset,
    Any,
}

impl<const EXACT: bool> From<u8> for Selector<EXACT> {
    fn from(value: u8) -> Self {
        if value & 0b1 != 0 {
            Selector::Set
        } else {
            Selector::Reset
        }
    }
}
impl<const EXACT: bool> From<u16> for Selector<EXACT> {
    fn from(value: u16) -> Self {
        (value as u8).into()
    }
}
impl<const EXACT: bool> From<u32> for Selector<EXACT> {
    fn from(value: u32) -> Self {
        (value as u8).into()
    }
}

impl<const EXACT: bool> Selector<EXACT> {
    pub fn into_value(&self) -> bool {
        match self {
            Selector::Set => true,
            Selector::Reset => false,
            Selector::Any => false,
        }
    }
    pub fn into_mask(&self) -> bool {
        match self {
            Selector::Set => EXACT,
            Selector::Reset => EXACT,
            Selector::Any => !EXACT,
        }
    }
}

/// A bitmask filter.
#[derive(Debug, Clone, Copy)]
pub struct BitSelector<const EXACT: bool, const N: usize> {
    pub bits: [Selector<EXACT>; N],
}

impl<const EXACT: bool, const N: usize> BitSelector<EXACT, N> {
    pub fn new(bits: [Selector<EXACT>; N]) -> Self {
        Self { bits }
    }
    pub fn new_any() -> Self {
        Self {
            bits: [Selector::Any; N],
        }
    }
}

pub trait BitSelectorNewExact<T, const EXACT: bool, const N: usize> {
    fn new_exact(value: T) -> BitSelector<EXACT, N>;
}

impl<const EXACT: bool> BitSelectorNewExact<u16, EXACT, 11> for BitSelector<EXACT, 11> {
    fn new_exact(mut value: u16) -> BitSelector<EXACT, 11> {
        let mut bits = [Selector::Any; 11];

        for bit in bits.iter_mut() {
            *bit = value.into();
            value >>= 1;
        }

        Self { bits }
    }
}
impl<const EXACT: bool> BitSelectorNewExact<u8, EXACT, 8> for BitSelector<EXACT, 8> {
    fn new_exact(mut value: u8) -> BitSelector<EXACT, 8> {
        let mut bits = [Selector::Any; 8];

        for bit in bits.iter_mut() {
            *bit = value.into();
            value >>= 1;
        }

        Self { bits }
    }
}
impl<const EXACT: bool> BitSelectorNewExact<u8, EXACT, 1> for BitSelector<EXACT, 1> {
    fn new_exact(mut value: u8) -> BitSelector<EXACT, 1> {
        let mut bits = [Selector::Any; 1];

        for bit in bits.iter_mut() {
            *bit = value.into();
            value >>= 1;
        }

        Self { bits }
    }
}

/// Trait to convert selector type into values and masks.
trait SelectorInto<T> {
    /// Convert the selector into the value portion of the filter.
    fn to_value(&self) -> T;
    /// Convert the selector into the mask portion of the filter.
    fn to_mask(&self) -> T;
}

impl<const EXACT: bool> SelectorInto<u8> for [Selector<EXACT>] {
    fn to_value(&self) -> u8 {
        let mut value: u8 = 0;

        for bit in self.iter().rev() {
            value = (value << 1) | (bit.into_value() as u8);
        }

        value
    }
    fn to_mask(&self) -> u8 {
        let mut mask: u8 = 0;

        // Fill the mask with bits that match against anything.
        for _ in 0..8 {
            mask = (mask << 1) | ((!EXACT) as u8);
        }

        // Insert the bits from the slice into the mask.
        for bit in self.iter().rev() {
            mask = (mask << 1) | (bit.into_mask() as u8);
        }

        mask
    }
}

#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(test)]
mod tests {
    use crate::{BitSelector, Selector, SelectorInto};

    #[test]
    fn bit_selector_example() {
        let filter: BitSelector<false, 8> = BitSelector::new([
            Selector::Reset,
            Selector::Set,
            Selector::Any,
            Selector::Set,
            Selector::Set,
            Selector::Reset,
            Selector::Set,
            Selector::Any,
        ]);

        let value = filter.bits[0..8].to_value();
        let mask = filter.bits[0..8].to_mask();

        assert!(value == 0b01011010);
        assert!(mask == 0b10000100);
    }

    #[test]
    fn selector_set_any() {
        let s: Selector<true> = Selector::Any;

        assert!(!s.into_value());
        assert!(!s.into_mask());
    }
    #[test]
    fn selector_reset_any() {
        let s: Selector<false> = Selector::Any;

        assert!(!s.into_value());
        assert!(s.into_mask());
    }

    #[test]
    fn any_value_mask_exact_clear() {
        let s: BitSelector<false, 8> = BitSelector::new([
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
        ]);

        let value = s.bits[0..8].to_value();
        let mask = s.bits[0..8].to_mask();

        println!("Value: {:?}", value);
        println!("Mask: {:?}", mask);

        assert!(value == 0);
        assert!(mask == 0xff);
    }
    #[test]
    fn any_value_mask_exact_set() {
        let s: BitSelector<true, 8> = BitSelector::new([
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
        ]);

        let value = s.bits[0..8].to_value();
        let mask = s.bits[0..8].to_mask();

        assert!(value == 0);
        assert!(mask == 0x00);
    }

    #[test]
    fn mixed_value_mask_exact_set() {
        let s: BitSelector<true, 8> = BitSelector::new([
            Selector::Set,
            Selector::Set,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
        ]);

        let value = s.bits[0..8].to_value();
        let mask = s.bits[0..8].to_mask();

        assert!(value == 0b00000011);
        assert!(mask == 0b00000011);
    }

    #[test]
    fn mixed_value_mask_exact_reset() {
        let s: BitSelector<false, 8> = BitSelector::new([
            Selector::Set,
            Selector::Set,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
            Selector::Any,
        ]);

        let value = s.bits[0..8].to_value();
        let mask = s.bits[0..8].to_mask();

        assert!(value == 0b00000011);
        assert!(mask == 0b11111100);
    }
}
