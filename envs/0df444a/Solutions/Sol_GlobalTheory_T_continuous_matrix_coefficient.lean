-- Prove2me | solution 1 for GlobalTheory.T.continuous_matrix_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:05:25.70853+00:00
-- url     : https://prove2.me/submissions/881f0afc-af2b-48ef-b3e6-17f1aefd4a77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMatrixCoefficient
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMatrixCoefficientStatement
import Theorems.Thm_GlobalTheory_RealWeil_continuous_matrixCoeff_rhoFun


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (g g' : Sch (Fin n)), Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) := by
  first | exact @GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun | exact GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun | (intros; apply GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun <;> assumption)
end _root_.GlobalTheory.T
