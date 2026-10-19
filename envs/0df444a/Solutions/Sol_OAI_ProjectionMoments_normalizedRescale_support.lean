-- Prove2me | solution 1 for OAI.ProjectionMoments.normalizedRescale_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:24:42.869482+00:00
-- url     : https://prove2.me/submissions/a2b59be6-a59d-4276-81c2-5525b347427e

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
theorem solution {ν : Measure E} (K a : ℝ) (z : E) {R : ℝ}
    (hR : 0 < R) (hsupport : ν.support ⊆ Metric.closedBall z R) :
    (normalizedRescale ν K a z R).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  unfold normalizedRescale
  apply Measure.ae_smul_measure
  have hmeas : Measurable (rescale z R) := by
    unfold rescale; fun_prop
  rw [ae_map_iff hmeas.aemeasurable measurableSet_closedBall]
  have hs : ∀ᵐ x ∂ν, x ∈ Metric.closedBall z R :=
    Filter.mem_of_superset (Measure.support_mem_ae (μ := ν)) hsupport
  filter_upwards [hs] with x hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  rw [dist_zero_right, rescale, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hR]
  rw [inv_mul_le_iff₀ hR, mul_one]; exact hx
