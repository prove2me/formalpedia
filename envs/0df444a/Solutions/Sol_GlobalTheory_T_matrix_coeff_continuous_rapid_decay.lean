-- Prove2me | solution 1 for GlobalTheory.T.matrix_coeff_continuous_rapid_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:48.209701+00:00
-- url     : https://prove2.me/submissions/aad4de0a-629e-4956-8fd7-23c00b401cdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffContinuousRapidDecay
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffContinuousRapidDecayStatement
import Theorems.Thm_GlobalTheory_matrixCoeff_continuous_rapidDecay


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
theorem _root_.solution : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) ∧
    ∀ N : ℕ, ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖w‖) ^ N ≤ C := by
  first | exact @GlobalTheory.matrixCoeff_continuous_rapidDecay | exact GlobalTheory.matrixCoeff_continuous_rapidDecay | (intros; apply GlobalTheory.matrixCoeff_continuous_rapidDecay <;> assumption)
end _root_.GlobalTheory.T
