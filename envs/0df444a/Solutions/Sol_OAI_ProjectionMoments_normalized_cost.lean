-- Prove2me | solution 1 for OAI.ProjectionMoments.normalized_cost
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:17:52.111172+00:00
-- url     : https://prove2.me/submissions/43750ce7-8658-4e7b-ab8a-339cdd5f85a7

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
theorem pm_ubv (k : ℕ) (hk : 1 ≤ k) :
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

theorem solution (d k n : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (hdk : d ≤ 32*k)
    (D : ℝ) (hD : 0 < D) :
    unitBallVolume k ^ n *
      ((2 : ℝ≥0∞)^k * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) *
        (ENNReal.ofReal (D^d)^(n+1) * (128 : ℝ≥0∞)^(d*n))) ≤
      ENNReal.ofReal ((16384 * max D 1)^(d*(n+1))) := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hV : unitBallVolume k ≤ ENNReal.ofReal ((6 / Real.sqrt k) ^ k) := by
    unfold unitBallVolume
    rw [Measure.addHaar_closedBall_eq_addHaar_ball]
    exact pm_ubv k hk
  set M := max D 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hDM : D ≤ M := le_max_left _ _
  calc unitBallVolume k ^ n *
      ((2 : ℝ≥0∞)^k * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) *
        (ENNReal.ofReal (D^d)^(n+1) * (128 : ℝ≥0∞)^(d*n)))
      ≤ ENNReal.ofReal ((6 / Real.sqrt k) ^ k) ^ n *
      ((2 : ℝ≥0∞)^k * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) *
        (ENNReal.ofReal (D^d)^(n+1) * (128 : ℝ≥0∞)^(d*n))) := by gcongr
    _ = ENNReal.ofReal (((6 / Real.sqrt k) ^ k) ^ n * ((2:ℝ)^k * Real.sqrt (2*d)^(k*n) *
          ((D^d)^(n+1) * (128:ℝ)^(d*n)))) := by
        have h6 : 0 ≤ 6 / Real.sqrt k := div_nonneg (by norm_num) (Real.sqrt_nonneg _)
        have e1 : (2:ℝ≥0∞)^k = ENNReal.ofReal ((2:ℝ)^k) := by
          rw [ENNReal.ofReal_pow (by norm_num)]; norm_num
        have e2 : (128:ℝ≥0∞)^(d*n) = ENNReal.ofReal ((128:ℝ)^(d*n)) := by
          rw [ENNReal.ofReal_pow (by norm_num)]; norm_num
        rw [← ENNReal.ofReal_pow (pow_nonneg h6 _), ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
          ← ENNReal.ofReal_pow (pow_nonneg hD.le _), e1, e2,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((16384 * M)^(d*(n+1))) := by
        apply ENNReal.ofReal_le_ofReal
        have h48 : 6 / Real.sqrt k * Real.sqrt (2 * d) ≤ 48 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (Real.sqrt_pos.2 hk0)]
          have h1 : Real.sqrt (2 * d) ≤ Real.sqrt (64 * k) := Real.sqrt_le_sqrt (by
            have : (d:ℝ) ≤ 32 * k := by exact_mod_cast hdk
            linarith)
          have h2 : Real.sqrt (64 * k) = 8 * Real.sqrt k := by
            rw [Real.sqrt_mul (by norm_num), show (64:ℝ) = 8^2 by norm_num, Real.sqrt_sq (by norm_num)]
          nlinarith [Real.sqrt_nonneg (k:ℝ)]
        have hA : ((6 / Real.sqrt k) ^ k) ^ n * Real.sqrt (2*d)^(k*n) ≤ (48:ℝ)^(d*n) := by
          rw [← pow_mul, ← mul_pow]
          calc (6 / Real.sqrt k * Real.sqrt (2 * d)) ^ (k * n) ≤ (48:ℝ)^(k*n) :=
                pow_le_pow_left₀ (by positivity) h48 _
            _ ≤ (48:ℝ)^(d*n) := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right _ hkd)
        have hB : (2:ℝ)^k ≤ (16384:ℝ)^d :=
          (pow_le_pow_right₀ (by norm_num) hkd).trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
        have hC : (D^d)^(n+1) ≤ M^(d*(n+1)) := by
          rw [← pow_mul]; exact pow_le_pow_left₀ hD.le hDM _
        have hE : (48:ℝ)^(d*n) * (128:ℝ)^(d*n) ≤ (16384:ℝ)^(d*n) := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
        calc ((6 / Real.sqrt k) ^ k) ^ n * ((2:ℝ)^k * Real.sqrt (2*d)^(k*n) *
              ((D^d)^(n+1) * (128:ℝ)^(d*n)))
            = (((6 / Real.sqrt k) ^ k) ^ n * Real.sqrt (2*d)^(k*n)) * (128:ℝ)^(d*n) * (2:ℝ)^k *
                (D^d)^(n+1) := by ring
          _ ≤ (48:ℝ)^(d*n) * (128:ℝ)^(d*n) * (16384:ℝ)^d * M^(d*(n+1)) := by gcongr
          _ ≤ (16384:ℝ)^(d*n) * (16384:ℝ)^d * M^(d*(n+1)) := by gcongr
          _ = (16384 * M)^(d*(n+1)) := by rw [mul_pow, mul_add, mul_one, pow_add]; ring
