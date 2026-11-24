-- Prove2me | solution 1 for GlobalTheory.T.schwartz_weighted_sobolev_bound_of_finrank_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:55.68626+00:00
-- url     : https://prove2.me/submissions/3c5beccc-63d9-494a-9e1d-683f9f374c48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzWeightedSobolevOfFinrankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzWeightedSobolevOfFinrankZeroStatement
import Theorems.Thm_GlobalTheory_schwartz_weighted_sobolev_of_finrank_zero


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
theorem _root_.solution : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], finrank ℝ E = 0 → ∀ (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by
  first | exact @GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero | exact GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero | (intros; apply GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero <;> assumption)
end _root_.GlobalTheory.T
