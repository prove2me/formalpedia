-- Prove2me | solution 2 for OAI.ProjectionMoments.ballAverage_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:12:16.30076+00:00
-- url     : https://prove2.me/submissions/fecb41de-8d3d-48e4-b141-98f9b30176d8

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Graph.lean:L143-L168
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.ballAverage_eq. The node keeps its source
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

section BallDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
lemma ballAverage_eq (ν : Measure E) [SFinite ν] (m : ℕ) (η : ℝ)
    (A : Fin m → E) (y : Label m) :
    ballAverage ν m η (A,y) =
      (ν.map (rowMap A)) (Metric.closedBall y η) /
        volume (Metric.closedBall y η) := by
  have he (t : E) :
      (fun j => WithLp.ofLp y j - ⟪t, A j⟫) = WithLp.ofLp (y - rowMap A t) := by
    simp only [rowMap_apply, WithLp.ofLp_sub]
    rfl
  have hpoint (t : E) :
      ballKernel m η (fun j => WithLp.ofLp y j - ⟪t, A j⟫) =
        (Metric.closedBall y η).indicator
          (fun _ => (volume (Metric.closedBall y η))⁻¹) (rowMap A t) := by
    rw [ballKernel, he, WithLp.toLp_ofLp, Measure.addHaar_closedBall_center volume y]
    have hh : y - rowMap A t ∈ Metric.closedBall (0 : Label m) η ↔
        rowMap A t ∈ Metric.closedBall y η := by
      simp [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    by_cases h : rowMap A t ∈ Metric.closedBall y η
    · simp only [Set.indicator_of_mem h, Set.indicator_of_mem (hh.mpr h)]
    · simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem (not_congr hh |>.mpr h)]
  simp only [ballAverage, vectorSmoothing, hpoint]
  rw [← lintegral_map (measurable_const.indicator Metric.isClosed_closedBall.measurableSet)
    (rowMap A).continuous.measurable,
    lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp [div_eq_mul_inv, mul_comm]

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


theorem solution : type_of% @_root_.OAI.ProjectionMoments.ballAverage_eq := @_root_.OAI.ProjectionMoments.ballAverage_eq
