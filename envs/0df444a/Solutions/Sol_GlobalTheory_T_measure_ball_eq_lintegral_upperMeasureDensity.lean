-- Prove2me | solution 1 for GlobalTheory.T.measure_ball_eq_lintegral_upperMeasureDensity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:37:17.831963+00:00
-- url     : https://prove2.me/submissions/fc1f849c-bc5c-41ca-9780-9262849fcca4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasureBallEqLintegralUpperMeasureDensity
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasureBallEqLintegralUpperMeasureDensityStatement
import Theorems.Thm_GlobalTheory_measure_ball_eq_lintegral_upperDens


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
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (η : ℝ) (C : ℝ≥0), (∀ x : V, ‖x‖ < η → GlobalTheory.HaarDensChart.upperDens l ν x < C) → ∀ ρ : ℝ, ρ ≤ η → ν (Metric.ball 0 ρ) = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
  first | exact @GlobalTheory.measure_ball_eq_lintegral_upperDens | exact GlobalTheory.measure_ball_eq_lintegral_upperDens | (intros; apply GlobalTheory.measure_ball_eq_lintegral_upperDens <;> assumption)
end _root_.GlobalTheory.T
