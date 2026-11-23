-- Prove2me | solution 1 for GlobalTheory.FormalInv.X_mem_weightGe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:46.526503+00:00
-- url     : https://prove2.me/submissions/257a34c6-7b6d-4b0c-a3e8-9a2b7cef75ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_apply
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_symm_apply
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inl
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_apply
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_symm_apply
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inl
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inr

set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable {σ' τ' : Type*}
namespace GlobalTheory.FormalInv
theorem _root_.solution (w : σ → ℕ) (s : σ) : (X s : MvPowerSeries σ R) ∈ weightGe w (w s) := by
  classical
  intro d hd
  rw [coeff_X, if_neg]
  rintro rfl
  simp [weight_single] at hd
end GlobalTheory.FormalInv
