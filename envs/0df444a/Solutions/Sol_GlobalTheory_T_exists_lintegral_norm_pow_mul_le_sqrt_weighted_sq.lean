-- Prove2me | solution 1 for GlobalTheory.T.exists_lintegral_norm_pow_mul_le_sqrt_weighted_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:27:12.03181+00:00
-- url     : https://prove2.me/submissions/0ad10efa-d87e-42fa-9f65-75ac018eb7ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralNormPowMulLeSqrtWeightedSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralNormPowMulLeSqrtWeightedSqStatement
import Theorems.Thm_GlobalTheory_lintegral_norm_pow_mul_le_sqrt_weighted_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [NormedAddCommGroup F], ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (H : E → F), Continuous H → ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) ∂μ ≤ C * (∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) ∂μ + ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  first | exact @GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq | exact GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq | (intros; apply GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq <;> assumption)
end _root_.GlobalTheory.T
