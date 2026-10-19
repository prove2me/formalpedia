-- Prove2me | solution 1 for OAI.ProjectionMoments.capReference_sum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:47:36.610987+00:00
-- url     : https://prove2.me/submissions/b87aea81-b741-4dbe-8bfc-bf7fe9426e5a

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
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
theorem pm_sum_le {α J : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset J)
    (f : J → α → ℝ≥0∞) : ∑ j ∈ s, ∫⁻ x, f j x ∂μ ≤ ∫⁻ x, ∑ j ∈ s, f j x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp only [Finset.sum_insert ha]
    calc (∫⁻ x, f a x ∂μ) + ∑ j ∈ s, ∫⁻ x, f j x ∂μ
        ≤ (∫⁻ x, f a x ∂μ) + ∫⁻ x, ∑ j ∈ s, f j x ∂μ := by gcongr
      _ ≤ ∫⁻ x, (f a x + ∑ j ∈ s, f j x) ∂μ := le_lintegral_add _ _

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {k : ℕ} {J : Type*} [Fintype J]
    (K : J → (Fin k → E) × Label k → ℝ≥0∞) (hK : ∀ j, Measurable (K j))
    (hKsum : ∀ z, ∑ j, K j z ≤ 1) (c : E) (r : ℝ) : ∑ j, capReference (K j) c r ≤ 1 := by
  have hU : unitBallLaw k Set.univ ≤ 1 := by
    unfold unitBallLaw
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]
    exact ENNReal.inv_mul_le_one _
  unfold capReference
  calc ∑ j, ∫⁻ X, ∫⁻ z, K j (X, capReferenceLabel c r X z) ∂unitBallLaw k ∂Measure.pi (fun _ => stdGaussian E)
      ≤ ∫⁻ X, ∑ j, ∫⁻ z, K j (X, capReferenceLabel c r X z) ∂unitBallLaw k
          ∂Measure.pi (fun _ => stdGaussian E) := pm_sum_le _ _ _
    _ ≤ ∫⁻ X, ∫⁻ z, ∑ j, K j (X, capReferenceLabel c r X z) ∂unitBallLaw k
          ∂Measure.pi (fun _ => stdGaussian E) := lintegral_mono (fun X => pm_sum_le _ _ _)
    _ ≤ ∫⁻ X, ∫⁻ z, 1 ∂unitBallLaw k ∂Measure.pi (fun _ => stdGaussian E) :=
          lintegral_mono (fun X => lintegral_mono (fun z => hKsum _))
    _ ≤ ∫⁻ X, 1 ∂Measure.pi (fun _ => stdGaussian E) := by
          apply lintegral_mono; intro X
          rw [lintegral_one]; exact hU
    _ = 1 := by rw [lintegral_one, measure_univ]
