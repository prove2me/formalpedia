-- Prove2me | solution 1 for GlobalTheory.T.dw_contDiffOn_local_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:44.310618+00:00
-- url     : https://prove2.me/submissions/079581da-e7c8-44cf-8a65-475ca69c6364

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinearStatement
import Theorems.Thm_GlobalTheory_HCA_dw_smooth_local_linear


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
theorem _root_.solution : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d)), (∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ (dw w u) U) ∧ (∀ u v : E d → ℂ, Set.EqOn u v U → Set.EqOn (dw w u) (dw w v) U) ∧ (∀ u v : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U → ∀ s t : ℂ, Set.EqOn (dw w (s • u + t • v)) (s • dw w u + t • dw w v) U) := by
  first | exact @GlobalTheory.HCA.dw_smooth_local_linear | exact GlobalTheory.HCA.dw_smooth_local_linear | (intros; apply GlobalTheory.HCA.dw_smooth_local_linear <;> assumption)
end _root_.GlobalTheory.T
