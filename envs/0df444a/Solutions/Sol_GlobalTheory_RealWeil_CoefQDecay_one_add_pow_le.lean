-- Prove2me | solution 1 for GlobalTheory.RealWeil.CoefQDecay.one_add_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:55:16.314862+00:00
-- url     : https://prove2.me/submissions/22acefe5-64b4-4d08-8bcc-baed0200a7e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPart

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
open scoped FourierTransform ContDiff RealInnerProductSpace Real
noncomputable section
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.CoefQDecay
variable {n : ℕ}
namespace GlobalTheory.RealWeil.CoefQDecay
theorem _root_.solution (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
  have h1 : 1 + t ≤ 2 * max 1 t := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max 1 t) ^ N ≤ 1 + t ^ N := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ht N]
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg ht N]
  calc (1 + t) ^ N ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by linarith) h1 N
    _ = 2 ^ N * (max 1 t) ^ N := mul_pow _ _ _
    _ ≤ 2 ^ N * (1 + t ^ N) := by gcongr
end GlobalTheory.RealWeil.CoefQDecay
