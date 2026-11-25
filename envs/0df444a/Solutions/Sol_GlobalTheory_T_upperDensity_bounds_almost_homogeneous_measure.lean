-- Prove2me | solution 1 for GlobalTheory.T.upperDensity_bounds_almost_homogeneous_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:48:14.558934+00:00
-- url     : https://prove2.me/submissions/a2f5c9ae-7bd0-4101-98a4-456263189ac8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDensityBoundsAlmostHomogeneousMeasure
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDensityBoundsAlmostHomogeneousMeasureStatement
import Theorems.Thm_GlobalTheory_upperDens_bounds_of_almost_homogeneous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (c : ℝ≥0∞), c ≠ ⊤ → Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) → ∀ ε η : ℝ, 0 < ε → ε < 1 → (∀ x : V, ‖x‖ < η → ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧ ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) → ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ V) * c ≤ GlobalTheory.HaarDensChart.upperDens l ν x ∧ GlobalTheory.HaarDensChart.upperDens l ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ V) * c := by
  first | exact @GlobalTheory.upperDens_bounds_of_almost_homogeneous | exact GlobalTheory.upperDens_bounds_of_almost_homogeneous | (intros; apply GlobalTheory.upperDens_bounds_of_almost_homogeneous <;> assumption)
end _root_.GlobalTheory.T
