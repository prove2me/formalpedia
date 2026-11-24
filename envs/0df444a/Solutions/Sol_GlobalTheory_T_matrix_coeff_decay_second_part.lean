-- Prove2me | solution 1 for GlobalTheory.T.matrix_coeff_decay_second_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:18:19.822893+00:00
-- url     : https://prove2.me/submissions/bff1e0ce-443f-41f0-a032-c31d18327d28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPartStatement
import Theorems.Thm_GlobalTheory_RealWeil_coef_qDecay


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
theorem _root_.solution : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖qPart w‖) ^ N ≤ C := by
  first | exact @GlobalTheory.RealWeil.coef_qDecay | exact GlobalTheory.RealWeil.coef_qDecay | (intros; apply GlobalTheory.RealWeil.coef_qDecay <;> assumption)
end _root_.GlobalTheory.T
