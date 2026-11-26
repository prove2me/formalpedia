-- Prove2me | solution 1 for MohP3.Wt.dd_apply_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:51:10.103305+00:00
-- url     : https://prove2.me/submissions/55006ade-b1f5-4639-8db8-14093e773d6b

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
attribute [local simp] MohP3.Wt.dd_apply_zero

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution (a b c : ℕ) : dd a b c 1 = b := by
  simp [dd]
end MohP3.Wt
