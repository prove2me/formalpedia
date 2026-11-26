-- Prove2me | solution 1 for MohP3.Wt.wt_dd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:53:07.94147+00:00
-- url     : https://prove2.me/submissions/dd67bacf-ca95-41ee-aa2a-7b293d137ba6

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution (a b c : ℕ) : wt (dd a b c) = 6 * a + 8 * b + 10 * c := by
  simp [wt]
end MohP3.Wt
