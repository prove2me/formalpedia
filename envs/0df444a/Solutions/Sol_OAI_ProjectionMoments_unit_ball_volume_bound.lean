-- Prove2me | solution 1 for OAI.ProjectionMoments.unit_ball_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:16:09.56799+00:00
-- url     : https://prove2.me/submissions/d467b9f1-4c68-436d-8815-07b35c19247a

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
theorem solution (k : ℕ) (hk : 1 ≤ k) :
    (volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1) ≤
      ENNReal.ofReal ((6 / Real.sqrt k)^k) := by
  set t : ℝ := (k : ℝ) / 2 with htdef
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ht : 0 < t := by positivity
  have hG := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin k)) ht
  rw [finrank_euclideanSpace_fin] at hG
  have hint : Integrable (fun v : EuclideanSpace ℝ (Fin k) => Real.exp (-t * ‖v‖ ^ 2)) := by
    by_contra h
    rw [integral_undef h] at hG
    have : (0 : ℝ) < (Real.pi / t) ^ ((k : ℝ) / 2) := by positivity
    linarith
  have h1 : (volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1) ≤
      ∫⁻ v : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (Real.exp t * Real.exp (-t * ‖v‖ ^ 2)) := by
    rw [← lintegral_indicator_one measurableSet_ball]
    apply lintegral_mono
    intro v
    by_cases hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1
    · rw [Set.indicator_of_mem hv, Pi.one_apply, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.exp_add]
      apply Real.one_le_exp
      rw [Metric.mem_ball, dist_zero_right] at hv
      have : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
      nlinarith
    · rw [Set.indicator_of_notMem hv]; exact bot_le
  have h2 : ∫⁻ v : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (Real.exp t * Real.exp (-t * ‖v‖ ^ 2)) =
      ENNReal.ofReal (Real.exp t * (Real.pi / t) ^ ((k : ℝ) / 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
      (Filter.Eventually.of_forall (fun v => by positivity)), integral_const_mul, hG]
  rw [h2] at h1
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  have he : Real.exp t = Real.exp 1 ^ t := (Real.exp_one_rpow t).symm
  have hpt : Real.pi / t = 2 * Real.pi / k := by rw [htdef]; field_simp
  have hk2 : ((k : ℝ) / 2) = t := rfl
  rw [he, hpt, hk2, ← Real.mul_rpow (by positivity) (by positivity)]
  have hR : (6 / Real.sqrt k) ^ k = (36 / (k : ℝ)) ^ t := by
    have hsq : (6 / Real.sqrt k) ^ 2 = 36 / (k : ℝ) := by
      rw [div_pow, Real.sq_sqrt hk0.le]; norm_num
    rw [← hsq, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; rw [htdef]; push_cast; ring
  rw [hR]
  apply Real.rpow_le_rpow (by positivity) _ ht.le
  have hpi := Real.pi_lt_d2
  have hexp := Real.exp_one_lt_d9
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hk0]
  nlinarith [Real.exp_pos 1, Real.pi_pos]
