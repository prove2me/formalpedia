-- Prove2me | solution 1 for MohP3.Wt.monomial_dd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:21:58.28843+00:00
-- url     : https://prove2.me/submissions/590335ca-2d12-4ac7-85ec-e8743fff3627

module
public import Mathlib
public import Definitions.Def_MohP3_Order

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution (a b c : ℕ) :
    (MvPowerSeries.monomial (dd a b c) (1 : k)) =
      (X 0) ^ a * (X 1) ^ b * (X 2) ^ c := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial, one_mul, one_mul]
  rfl
end MohP3.Wt
