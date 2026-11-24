-- Prove2me | solution 1 for GlobalTheory.T.exists_continuous_functional_iterPartialDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:07:01.266668+00:00
-- url     : https://prove2.me/submissions/f160d109-f1ce-4aa5-b9c2-da3ce7dc05a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDerivStatement
import Theorems.Thm_GlobalTheory_HCA_dw_continuousFunctional


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (R : B →ₗ[ℂ] (E d → ℂ)), (∀ x ∈ U, Continuous fun u => R u x) → (∀ u, ContDiffOn ℝ ∞ (R u) U) → ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : B →L[ℂ] ℂ, ∀ u, l u = dw w (R u) x := by
  first | exact @GlobalTheory.HCA.dw_continuousFunctional | exact GlobalTheory.HCA.dw_continuousFunctional | (intros; apply GlobalTheory.HCA.dw_continuousFunctional <;> assumption)
end _root_.GlobalTheory.T
