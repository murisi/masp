use borsh::{BorshDeserialize, BorshSerialize};
use serde::{Deserialize, Serialize};
use std::iter::Sum;
use std::ops::{Add, AddAssign, Sub, SubAssign};
use std::collections::BTreeMap;
use crate::transaction::AssetType;
use std::convert::TryInto;

const COIN: i64 = 1_0000_0000;
const MAX_MONEY: i64 = 21_000_000 * COIN;
const ZEC: AssetType = AssetType::from_identifier(&[0;32]).unwrap();

pub const DEFAULT_FEE: Amount = Amount::from_u64(ZEC, 10000).unwrap();

/// A type-safe representation of some quantity of Zcash.
///
/// An Amount can only be constructed from an integer that is within the valid monetary
/// range of `{-MAX_MONEY..MAX_MONEY}` (where `MAX_MONEY` = 21,000,000 × 10⁸ zatoshis).
/// However, this range is not preserved as an invariant internally; it is possible to
/// add two valid Amounts together to obtain an invalid Amount. It is the user's
/// responsibility to handle the result of serializing potentially-invalid Amounts. In
/// particular, a [`Transaction`] containing serialized invalid Amounts will be rejected
/// by the network consensus rules.
///
/// [`Transaction`]: crate::transaction::Transaction
#[derive(
    Clone, Debug, PartialEq, BorshSerialize, BorshDeserialize, Serialize, Deserialize, PartialOrd, Eq, Ord, Hash
)]
pub struct Amount(BTreeMap<AssetType, i64>);

impl Amount {
    /// Returns a zero-valued Amount.
    pub const fn zero() -> Self {
        Amount(BTreeMap::new())
    }

    /// Creates an Amount from an i64.
    ///
    /// Returns an error if the amount is outside the range `{-MAX_MONEY..MAX_MONEY}`.
    pub fn from_i64(atype: AssetType, amount: i64) -> Result<Self, ()> {
        if -MAX_MONEY <= amount && amount <= MAX_MONEY {
            let ret = BTreeMap::new();
            ret[&atype] = amount;
            Ok(Amount(ret))
        } else {
            Err(())
        }
    }

    /// Creates a non-negative Amount from an i64.
    ///
    /// Returns an error if the amount is outside the range `{0..MAX_MONEY}`.
    pub fn from_nonnegative_i64(atype: AssetType, amount: i64) -> Result<Self, ()> {
        if 0 <= amount && amount <= MAX_MONEY {
            let ret = BTreeMap::new();
            ret[&atype] = amount;
            Ok(Amount(ret))
        } else {
            Err(())
        }
    }

    /// Creates an Amount from a u64.
    ///
    /// Returns an error if the amount is outside the range `{0..MAX_MONEY}`.
    pub fn from_u64(atype: AssetType, amount: u64) -> Result<Self, ()> {
        if amount <= MAX_MONEY as u64 {
            let ret = BTreeMap::new();
            ret[&atype] = amount as i64;
            Ok(Amount(ret))
        } else {
            Err(())
        }
    }

    /// Reads an Amount from a signed 64-bit little-endian integer.
    ///
    /// Returns an error if the amount is outside the range `{-MAX_MONEY..MAX_MONEY}`.
    pub fn from_i64_le_bytes(bytes: [u8; 40]) -> Result<Self, ()> {
        let atype = AssetType::from_identifier(&bytes[..32].try_into().unwrap()).ok_or(())?;
        let amount = i64::from_le_bytes(bytes[32..].try_into().unwrap());
        Amount::from_i64(atype, amount)
    }

    /// Reads a non-negative Amount from a signed 64-bit little-endian integer.
    ///
    /// Returns an error if the amount is outside the range `{0..MAX_MONEY}`.
    pub fn from_nonnegative_i64_le_bytes(bytes: [u8; 40]) -> Result<Self, ()> {
        let atype = AssetType::from_identifier(&bytes[..32].try_into().unwrap()).ok_or(())?;
        let amount = i64::from_le_bytes(bytes[32..].try_into().unwrap());
        Amount::from_nonnegative_i64(atype, amount)
    }

    /// Reads an Amount from an unsigned 64-bit little-endian integer.
    ///
    /// Returns an error if the amount is outside the range `{0..MAX_MONEY}`.
    pub fn from_u64_le_bytes(bytes: [u8; 40]) -> Result<Self, ()> {
        let atype = AssetType::from_identifier(&bytes[..32].try_into().unwrap()).ok_or(())?;
        let amount = u64::from_le_bytes(bytes[32..].try_into().unwrap());
        Amount::from_u64(atype, amount)
    }

    /*/// Returns the Amount encoded as a signed 64-bit little-endian integer.
    pub fn to_i64_le_bytes(self) -> [u8; 8] {
        self.0.to_le_bytes()
    }

    /// Returns `true` if `self` is positive and `false` if the Amount is zero or
    /// negative.
    pub const fn is_positive(self) -> bool {
        self.0.is_positive()
    }

    /// Returns `true` if `self` is negative and `false` if the Amount is zero or
    /// positive.
    pub const fn is_negative(self) -> bool {
        self.0.is_negative()
    }*/
}

/*impl From<Amount> for i64 {
    fn from(amount: Amount) -> i64 {
        amount.0
    }
}

impl From<Amount> for u64 {
    fn from(amount: Amount) -> u64 {
        amount.0 as u64
    }
}*/

impl Add<Amount> for Amount {
    type Output = Amount;

    fn add(self, rhs: Amount) -> Amount {
        let ret = self.clone();
        for (atype, amount) in rhs.0 {
            ret.0.entry(atype).or_insert(0);
            ret.0[&atype] += amount;
        }
        ret
        //Amount::from_i64(self.0 + rhs.0).expect("addition should remain in range")
    }
}

impl AddAssign<Amount> for Amount {
    fn add_assign(&mut self, rhs: Amount) {
        *self = *self + rhs
    }
}

impl Sub<Amount> for Amount {
    type Output = Amount;

    fn sub(self, rhs: Amount) -> Amount {
        let ret = self.clone();
        for (atype, amount) in rhs.0 {
            ret.0.entry(atype).or_insert(0);
            ret.0[&atype] -= amount;
        }
        ret
        //Amount::from_i64(self.0 - rhs.0).expect("subtraction should remain in range")
    }
}

impl SubAssign<Amount> for Amount {
    fn sub_assign(&mut self, rhs: Amount) {
        *self = *self - rhs
    }
}

impl Sum for Amount {
    fn sum<I: Iterator<Item = Amount>>(iter: I) -> Amount {
        iter.fold(Amount::zero(), Add::add)
    }
}

#[cfg(test)]
mod tests {
    use super::{Amount, MAX_MONEY, ZEC};

    /*#[test]
    fn amount_in_range() {
        let zero = b"\x00\x00\x00\x00\x00\x00\x00\x00";
        assert_eq!(Amount::from_u64_le_bytes(zero.clone()).unwrap(), Amount(0));
        assert_eq!(
            Amount::from_nonnegative_i64_le_bytes(zero.clone()).unwrap(),
            Amount(0)
        );
        assert_eq!(Amount::from_i64_le_bytes(zero.clone()).unwrap(), Amount(0));

        let neg_one = b"\xff\xff\xff\xff\xff\xff\xff\xff";
        assert!(Amount::from_u64_le_bytes(neg_one.clone()).is_err());
        assert!(Amount::from_nonnegative_i64_le_bytes(neg_one.clone()).is_err());
        assert_eq!(
            Amount::from_i64_le_bytes(neg_one.clone()).unwrap(),
            Amount(-1)
        );

        let max_money = b"\x00\x40\x07\x5a\xf0\x75\x07\x00";
        assert_eq!(
            Amount::from_u64_le_bytes(max_money.clone()).unwrap(),
            Amount(MAX_MONEY)
        );
        assert_eq!(
            Amount::from_nonnegative_i64_le_bytes(max_money.clone()).unwrap(),
            Amount(MAX_MONEY)
        );
        assert_eq!(
            Amount::from_i64_le_bytes(max_money.clone()).unwrap(),
            Amount(MAX_MONEY)
        );

        let max_money_p1 = b"\x01\x40\x07\x5a\xf0\x75\x07\x00";
        assert!(Amount::from_u64_le_bytes(max_money_p1.clone()).is_err());
        assert!(Amount::from_nonnegative_i64_le_bytes(max_money_p1.clone()).is_err());
        assert!(Amount::from_i64_le_bytes(max_money_p1.clone()).is_err());

        let neg_max_money = b"\x00\xc0\xf8\xa5\x0f\x8a\xf8\xff";
        assert!(Amount::from_u64_le_bytes(neg_max_money.clone()).is_err());
        assert!(Amount::from_nonnegative_i64_le_bytes(neg_max_money.clone()).is_err());
        assert_eq!(
            Amount::from_i64_le_bytes(neg_max_money.clone()).unwrap(),
            Amount(-MAX_MONEY)
        );

        let neg_max_money_m1 = b"\xff\xbf\xf8\xa5\x0f\x8a\xf8\xff";
        assert!(Amount::from_u64_le_bytes(neg_max_money_m1.clone()).is_err());
        assert!(Amount::from_nonnegative_i64_le_bytes(neg_max_money_m1.clone()).is_err());
        assert!(Amount::from_i64_le_bytes(neg_max_money_m1.clone()).is_err());
    }*/

    #[test]
    #[should_panic]
    fn add_panics_on_overflow() {
        let v = Amount::from_i64(ZEC, MAX_MONEY).unwrap();
        let _sum = v + Amount::from_i64(ZEC, 1).unwrap();
    }

    #[test]
    #[should_panic]
    fn add_assign_panics_on_overflow() {
        let mut a = Amount::from_i64(ZEC, MAX_MONEY).unwrap();
        a += Amount::from_i64(ZEC, 1).unwrap();
    }

    #[test]
    #[should_panic]
    fn sub_panics_on_underflow() {
        let v = Amount::from_i64(ZEC, -MAX_MONEY).unwrap();
        let _diff = v - Amount::from_i64(ZEC, 1).unwrap();
    }

    #[test]
    #[should_panic]
    fn sub_assign_panics_on_underflow() {
        let mut a = Amount::from_i64(ZEC, -MAX_MONEY).unwrap();
        a -= Amount::from_i64(ZEC, 1).unwrap();
    }
}
