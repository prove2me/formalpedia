-- Prove2me | solution 1 for MohP3.Wt.dd_apply_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:52:02.933528+00:00
-- url     : https://prove2.me/submissions/40f75e0c-1464-453c-8d42-0c8532993acb

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.dd_apply_one

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution (a b c : ℕ) : dd a b c 2 = c := by
  simp [dd]
end MohP3.Wt
