-- Prove2me | solution 1 for GlobalTheory.T.ofReal_norm_pow_mul_le_lintegral_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:57.981271+00:00
-- url     : https://prove2.me/submissions/3c68132f-3a58-4938-9d59-d89aa61e080f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLintegralSobolevPointwise
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLintegralSobolevPointwiseStatement
import Theorems.Thm_GlobalTheory_weighted_lintegral_sobolev_pointwise


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
theorem _root_.solution : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ), finrank ℝ E = m + 1 → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F), ContDiff ℝ (⊤ : ℕ∞) G → (∀ j ≤ m, Tendsto (iteratedFDeriv ℝ j G) (cocompact E) (𝓝 0)) → ∀ (k : ℕ) (x : E), ENNReal.ofReal (‖x‖ ^ k * ‖G x‖) ≤ C * ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖iteratedFDeriv ℝ (m + 1) G z‖) ∂μ := by
  first | exact @GlobalTheory.weighted_lintegral_sobolev_pointwise | exact GlobalTheory.weighted_lintegral_sobolev_pointwise | (intros; apply GlobalTheory.weighted_lintegral_sobolev_pointwise <;> assumption)
end _root_.GlobalTheory.T
