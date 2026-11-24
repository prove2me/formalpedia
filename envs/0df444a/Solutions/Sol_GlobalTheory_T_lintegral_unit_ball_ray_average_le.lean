-- Prove2me | solution 1 for GlobalTheory.T.lintegral_unit_ball_ray_average_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:30.966159+00:00
-- url     : https://prove2.me/submissions/a8844f9c-38e4-4248-af44-f6452ffd1696

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralUnitBallRayAverageLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralUnitBallRayAverageLeStatement
import Theorems.Thm_GlobalTheory_rayAvg_bound


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
theorem _root_.solution : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (Ψ : E → ℝ≥0∞) (m : ℕ), Measurable Ψ → finrank ℝ E = m + 1 → ∫⁻ v in Metric.closedBall (0:E) 1, ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂volume ∂μ ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ := by
  first | exact @GlobalTheory.rayAvg_bound | exact GlobalTheory.rayAvg_bound | (intros; apply GlobalTheory.rayAvg_bound <;> assumption)
end _root_.GlobalTheory.T
