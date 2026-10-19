-- Prove2me | solution 1 for OAI.ProjectionMoments.lowerDensity_is_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:12:27.657+00:00
-- url     : https://prove2.me/submissions/a82dd03a-c3a3-4546-824f-180944d0e774

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
theorem pm_ballAvg (ν : Measure E) [SFinite ν] (m : ℕ) (η : ℝ)
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


theorem solution (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (hA : ν.map (rowMap A) ≪ (volume : Measure (Label m))) :
    volume.withDensity (fun y => lowerDensity ν m (A,y)) = ν.map (rowMap A) := by
  set ρ := ν.map (rowMap A)
  have hdiff := Besicovitch.ae_tendsto_rnDeriv ρ (volume : Measure (Label m))
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
    · simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · simp only [Set.mem_Ioi]; positivity
  have hae : (fun y => lowerDensity ν m (A, y)) =ᵐ[volume] ρ.rnDeriv volume := by
    filter_upwards [hdiff] with y hy
    unfold lowerDensity
    simp only [pm_ballAvg]
    exact (hy.comp hr).liminf_eq
  rw [withDensity_congr_ae hae]
  exact Measure.withDensity_rnDeriv_eq ρ volume hA
