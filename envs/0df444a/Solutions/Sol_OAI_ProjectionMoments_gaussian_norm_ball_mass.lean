-- Prove2me | solution 1 for OAI.ProjectionMoments.gaussian_norm_ball_mass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:11:06.299995+00:00
-- url     : https://prove2.me/submissions/f48f190a-759f-4d8e-b708-46c23a0b050f

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
theorem solution (hd : 0 < Module.finrank ℝ E) :
    (2 : ℝ≥0∞)⁻¹ ≤ stdGaussian E (Metric.closedBall 0 (Real.sqrt (2 * Module.finrank ℝ E))) := by
  set d := Module.finrank ℝ E
  set μ := stdGaussian E
  let b := stdOrthonormalBasis ℝ E
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  -- second moments of coordinates
  have hcoord : ∀ i, ∫ x, (⟪b i, x⟫) ^ 2 ∂μ = 1 := by
    intro i
    let L : StrongDual ℝ E := innerSL ℝ (b i)
    have hL : ∀ x, L x = ⟪b i, x⟫ := fun x => rfl
    have hvar := variance_dual_stdGaussian L
    have hmean : μ[L] = 0 := integral_strongDual_stdGaussian L
    rw [variance_of_integral_eq_zero L.continuous.aemeasurable hmean] at hvar
    have hnorm : ‖L‖ = 1 := by
      simp only [L, innerSL_apply_norm]; exact b.orthonormal.1 i
    rw [hnorm] at hvar
    simpa [hL] using hvar
  have hint : ∀ i, Integrable (fun x => (⟪b i, x⟫) ^ 2) μ := by
    intro i
    exact (IsGaussian.memLp_dual μ (innerSL ℝ (b i)) 2 (by norm_num)).integrable_sq
  have hsq : ∫ x, ‖x‖ ^ 2 ∂μ = d := by
    have : (fun x : E => ‖x‖ ^ 2) = fun x => ∑ i, (⟪b i, x⟫) ^ 2 := by
      funext x; rw [b.sum_sq_inner_right]
    rw [this, integral_finset_sum _ (fun i _ => hint i)]
    simp [hcoord, d]
  have hintsq : Integrable (fun x : E => ‖x‖ ^ 2) μ := by
    have : (fun x : E => ‖x‖ ^ 2) = fun x => ∑ i, (⟪b i, x⟫) ^ 2 := by
      funext x; rw [b.sum_sq_inner_right]
    rw [this]; exact integrable_finset_sum _ (fun i _ => hint i)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖x‖)) hintsq (2 * d)
  rw [hsq] at hmarkov
  have hA : μ.real {x | 2 * (d : ℝ) ≤ ‖x‖ ^ 2} ≤ 1 / 2 := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have hsub : (Metric.closedBall (0 : E) (Real.sqrt (2 * d)))ᶜ ⊆ {x | 2 * (d : ℝ) ≤ ‖x‖ ^ 2} := by
    intro x hx
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
    simp only [Set.mem_setOf_eq]
    have h0 : 0 ≤ Real.sqrt (2 * d) := Real.sqrt_nonneg _
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * d by positivity)
    nlinarith
  have hB : μ.real (Metric.closedBall (0 : E) (Real.sqrt (2 * d)))ᶜ ≤ 1 / 2 :=
    (measureReal_mono hsub).trans hA
  rw [probReal_compl_eq_one_sub measurableSet_closedBall] at hB
  rw [← ofReal_measureReal, show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
  exact ENNReal.ofReal_le_ofReal (by linarith)

