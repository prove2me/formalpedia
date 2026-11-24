-- Prove2me | solution 1 for GlobalTheory.T.matrix_coeff_decay_first_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:29.9638+00:00
-- url     : https://prove2.me/submissions/2b9f53c5-4733-4154-82f6-e067dcc68a8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecayFirstPart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecayFirstPartStatement
import Theorems.Thm_GlobalTheory_matrixCoeff_pPart_decay


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
theorem _root_.solution : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖pPart w‖) ^ N ≤ C := by
  first | exact @GlobalTheory.matrixCoeff_pPart_decay | exact GlobalTheory.matrixCoeff_pPart_decay | (intros; apply GlobalTheory.matrixCoeff_pPart_decay <;> assumption)
end _root_.GlobalTheory.T
