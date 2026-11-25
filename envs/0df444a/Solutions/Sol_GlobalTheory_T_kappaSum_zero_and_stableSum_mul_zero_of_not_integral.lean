-- Prove2me | solution 1 for GlobalTheory.T.kappaSum_zero_and_stableSum_mul_zero_of_not_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:22:14.52513+00:00
-- url     : https://prove2.me/submissions/d8431831-c614-43d4-b7d8-c24ee03534a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegralStatement
import Theorems.Thm_GlobalTheory_UnitLemma_kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), ¬ (IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g) → InvAlg.kapSum B₁ B₂ = 0 ∧ B₁.stSum * B₂.stSum = 0 := by
  first | exact @GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral | exact GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral | (intros; apply GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral <;> assumption)
end _root_.GlobalTheory.T
