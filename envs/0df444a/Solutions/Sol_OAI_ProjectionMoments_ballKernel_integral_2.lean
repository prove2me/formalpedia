-- Prove2me | solution 2 for OAI.ProjectionMoments.ballKernel_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:10:46.657857+00:00
-- url     : https://prove2.me/submissions/8203d3aa-b57f-483f-b981-6fffc3b52e9c

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Graph.lean:L111-L124
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.ballKernel_integral. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Probability.ProjectionMoments.Graph ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments

section GaussianGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianGraph

lemma ballKernel_integral (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∫⁻ y, ballKernel m η y = 1 := by
  have hm : Measurable ((Metric.closedBall (0 : Label m) η).indicator
      (fun _ => (volume (Metric.closedBall (0 : Label m) η))⁻¹)) :=
    measurable_const.indicator Metric.isClosed_closedBall.measurableSet
  change (∫⁻ y, (Metric.closedBall (0 : Label m) η).indicator
    (fun _ => (volume (Metric.closedBall (0 : Label m) η))⁻¹) (WithLp.toLp 2 y)) = 1
  rw [(PiLp.volume_preserving_toLp (Fin m)).lintegral_comp hm,
    lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp only [lintegral_const, Measure.restrict_apply_univ]
  apply ENNReal.inv_mul_cancel
  · exact ne_of_gt ((Metric.isOpen_ball.measure_pos volume
      (Metric.nonempty_ball.mpr hη)).trans_le (measure_mono Metric.ball_subset_closedBall))
  · exact (isCompact_closedBall (0 : Label m) η).measure_lt_top.ne

section BallDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end BallDensity

section Rescaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Rescaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments
end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.ballKernel_integral := @_root_.OAI.ProjectionMoments.ballKernel_integral
