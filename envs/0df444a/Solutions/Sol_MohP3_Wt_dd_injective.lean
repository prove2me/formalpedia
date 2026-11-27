-- Prove2me | solution 1 for MohP3.Wt.dd_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:21:46.873332+00:00
-- url     : https://prove2.me/submissions/5110be70-0a49-4bd8-a5b2-d56ee0157563

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_wt_dd
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two
attribute [local simp] MohP3.Wt.wt_dd

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution {a b c a' b' c' : ℕ} (h : dd a b c = dd a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (fun d => d 0) h
  · simpa using congrArg (fun d => d 1) h
  · simpa using congrArg (fun d => d 2) h
end MohP3.Wt
