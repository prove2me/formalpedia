-- Prove2me | solution 1 for OAI.ProjectionMoments.ballKernel_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:24:49.705979+00:00
-- url     : https://prove2.me/submissions/0c02de64-1b70-4079-8a49-263ed8a518c6

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
theorem solution (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∫⁻ y, ballKernel m η y = 1 := by
  have hmeas : MeasurableSet ((WithLp.toLp 2 : (Fin m → ℝ) → Label m) ⁻¹' Metric.closedBall 0 η) :=
    measurableSet_closedBall.preimage (PiLp.volume_preserving_toLp (Fin m)).measurable
  have h1 : (fun y : Fin m → ℝ => ballKernel m η y) =
      ((WithLp.toLp 2 : (Fin m → ℝ) → Label m) ⁻¹' Metric.closedBall 0 η).indicator
        (fun _ => (volume (Metric.closedBall (0 : Label m) η))⁻¹) := by
    funext y; rfl
  rw [h1, lintegral_indicator_const hmeas,
    (PiLp.volume_preserving_toLp (Fin m)).measure_preimage measurableSet_closedBall.nullMeasurableSet]
  apply ENNReal.inv_mul_cancel
  · exact (Metric.measure_closedBall_pos volume 0 hη).ne'
  · exact (isCompact_closedBall (0 : Label m) η).measure_lt_top.ne
