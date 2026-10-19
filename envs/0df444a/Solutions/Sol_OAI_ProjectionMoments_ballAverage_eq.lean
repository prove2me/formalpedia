-- Prove2me | solution 1 for OAI.ProjectionMoments.ballAverage_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:28:57.651487+00:00
-- url     : https://prove2.me/submissions/fa046052-3de2-4416-a535-00543894eac1

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] in
theorem solution (ν : Measure E) [SFinite ν] (m : ℕ) (η : ℝ)
    (A : Fin m → E) (y : Label m) :
    ballAverage ν m η (A,y) =
      (ν.map (rowMap A)) (Metric.closedBall y η) /
        volume (Metric.closedBall y η) := by
  set c := (volume (Metric.closedBall (0 : Label m) η))⁻¹
  have hmeas : Measurable (rowMap A) := (rowMap A).continuous.measurable
  have hpt : ∀ t : E, ballKernel m η (fun j => (WithLp.ofLp y) j - ⟪t, A j⟫) =
      (rowMap A ⁻¹' Metric.closedBall y η).indicator (fun _ => c) t := by
    intro t
    have hv : WithLp.toLp 2 (fun j => (WithLp.ofLp y) j - ⟪t, A j⟫) = y - rowMap A t := by
      ext j; simp [rowMap, real_inner_comm]
    unfold ballKernel
    rw [hv]
    simp only [Set.indicator, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, c]
    rw [← dist_eq_norm, dist_comm]
  unfold ballAverage vectorSmoothing
  simp only [hpt]
  rw [lintegral_indicator_const (measurableSet_closedBall.preimage hmeas),
    Measure.map_apply hmeas measurableSet_closedBall, Measure.addHaar_closedBall_center,
    ENNReal.div_eq_inv_mul]

