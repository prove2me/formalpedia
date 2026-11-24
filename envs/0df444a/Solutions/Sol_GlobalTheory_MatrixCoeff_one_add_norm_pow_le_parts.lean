-- Prove2me | solution 1 for GlobalTheory.MatrixCoeff.one_add_norm_pow_le_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:13:25.491893+00:00
-- url     : https://prove2.me/submissions/58fbbd40-19a8-4e5d-a963-7eb806c1a585

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMatrixCoefficientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecayFirstPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffContinuousRapidDecay
import Theorems.Thm_GlobalTheory_MatrixCoeff_norm_le_max_parts

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
open GlobalTheory
open GlobalTheory.MatrixCoeff
namespace GlobalTheory.MatrixCoeff
theorem _root_.solution (n N : ℕ) (w : Fin n ⊕ Fin n → ℝ) :
    (1 + ‖w‖) ^ N ≤ (1 + ‖pPart w‖) ^ N + (1 + ‖qPart w‖) ^ N := by
  have h := norm_le_max_parts n w
  rcases le_total ‖pPart w‖ ‖qPart w‖ with h' | h'
  · rw [max_eq_right h'] at h
    have : (1 + ‖w‖) ^ N ≤ (1 + ‖qPart w‖) ^ N := by gcongr
    linarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖pPart w‖) N]
  · rw [max_eq_left h'] at h
    have : (1 + ‖w‖) ^ N ≤ (1 + ‖pPart w‖) ^ N := by gcongr
    linarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖qPart w‖) N]
end GlobalTheory.MatrixCoeff
