-- Prove2me | solution 1 for GlobalTheory.FormalInv.substInv_sumFamily
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:47:33.271855+00:00
-- url     : https://prove2.me/submissions/b590cc49-d46a-4269-b36f-e1834b88f9a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_eq_substInv_of_right
import Theorems.Thm_GlobalTheory_FormalInv_constantCoeff_sumFamily
import Theorems.Thm_GlobalTheory_FormalInv_subst_sumFamily_sumFamily
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable {σ' τ' : Type*}
namespace GlobalTheory.FormalInv
theorem _root_.solution [Fintype σ] [Fintype σ'] [DecidableEq σ] [DecidableEq σ']
    {a : σ → MvPowerSeries σ R} {a' : σ' → MvPowerSeries σ' R}
    (ha : ∀ i, constantCoeff (a i) = 0) (ha' : ∀ j, constantCoeff (a' j) = 0)
    (hA : IsUnit (linearPart a)) (hA' : IsUnit (linearPart a')) :
    IsUnit (linearPart (sumFamily a a')) ∧
      substInv (sumFamily a a') = sumFamily (substInv a) (substInv a') := by
  have h0 := constantCoeff_sumFamily (constantCoeff_substInv ha) (constantCoeff_substInv ha')
  have h : ∀ s, (sumFamily a a' s).subst (sumFamily (substInv a) (substInv a')) = X s := by
    intro s
    rw [subst_sumFamily_sumFamily _ _ (constantCoeff_substInv ha) (constantCoeff_substInv ha'),
      funext (subst_substInv_right ha hA), funext (subst_substInv_right ha' hA'), sumFamily_X]
  exact ⟨IsUnit.of_mul_eq_one _ (linearPart_mul_eq_one (constantCoeff_sumFamily ha ha') h0 h),
    (eq_substInv_of_right (constantCoeff_sumFamily ha ha') h0 h).symm⟩
end GlobalTheory.FormalInv
