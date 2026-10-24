-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.translated_row_expansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:24:51.460789+00:00
-- url     : https://prove2.me/submissions/eac17d39-98f4-45f3-8d16-dec1c861d9aa

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open OAI.PiExponent.FinitePeriodCollision

namespace E103TR

theorem h_le (center : ℂ) (R : ℝ) (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (z : ℂ) (hz : ‖z‖ = 1 / 2) :
    ‖(center + Complex.log (1 + z)) / (R : ℂ)‖ ≤ 1 / 2 := by
  have hlog : ‖Complex.log (1 + z)‖ ≤ 3 / 4 := by
    have := Complex.norm_log_one_add_half_le_self (z := z) (by rw [hz])
    rw [hz] at this; linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_le_iff₀ hR]
  calc ‖center + Complex.log (1 + z)‖ ≤ ‖center‖ + ‖Complex.log (1 + z)‖ := norm_add_le _ _
    _ ≤ 1 / 2 * R := by linarith

theorem coeff_le (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R) (D : ℝ)
    (hfD : ∀ z, z ∈ Metric.sphere (0 : ℂ) R → ‖f z‖ ≤ D) (d : ℕ) :
    ‖cauchyPowerSeries f 0 R d (fun _ => (R : ℂ))‖ ≤ D := by
  rw [cauchyPowerSeries_apply, norm_smul]
  have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) R,
      ‖((R : ℂ) / (z - 0)) ^ d • (z - 0)⁻¹ • f z‖ ≤ R⁻¹ * D := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    simp only [sub_zero, smul_eq_mul, norm_mul, norm_pow, norm_div, norm_inv, hz,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_self hR.ne', one_pow, one_mul]
    exact mul_le_mul_of_nonneg_left (hfD z (by rw [mem_sphere_zero_iff_norm, hz])) (by positivity)
  have hI := circleIntegral.norm_integral_le_of_norm_le_const hR.le hbd
  have h2 : ‖(2 * ↑Real.pi * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [h2]
  calc (2 * Real.pi)⁻¹ * _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * R * (R⁻¹ * D)) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = D := by field_simp

theorem series_eq (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R) (d : ℕ) (w : ℂ) :
    cauchyPowerSeries f 0 R d (fun _ => w) =
      (w / (R : ℂ)) ^ d * cauchyPowerSeries f 0 R d (fun _ => (R : ℂ)) := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have : (fun _ : Fin d => w) = fun _ => (w / (R : ℂ)) • (R : ℂ) := by
    ext; rw [smul_eq_mul, div_mul_cancel₀ _ hR']
  rw [this, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

end E103TR

theorem solution
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (R : NNReal) (hR : 0 < R) (D : ℝ) (hD : 0 ≤ D)
    (hfD : ∀ z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖f z‖ ≤ D)
    (center : ℂ) (hc : ‖center‖ + 3 / 4 ≤ (R : ℝ) / 2) (ell : ℕ) :
    HasSum
      (fun d =>
        rowTest ell
          (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d) *
          cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ)))
      (rowTest ell (fun t => f (center + Complex.log (1 + t)))) := by
  have hR0 : (0 : ℝ) < R := hR
  have hser : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 ⊤ :=
    hf.hasFPowerSeriesOnBall 0 hR
  have hpt : ∀ t : ℂ, HasSum (fun d => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d *
      cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ))) (f (center + Complex.log (1 + t))) := by
    intro t
    have := hser.hasSum (y := center + Complex.log (1 + t)) (by simp)
    rw [zero_add] at this
    have e : (fun n => cauchyPowerSeries f 0 (R : ℝ) n (fun _ => center + Complex.log (1 + t))) =
        fun d => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d *
          cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ)) :=
      funext fun d => E103TR.series_eq f R hR0 d _
    rw [e] at this
    exact this
  have hcomm : ∀ d, rowTest ell
        (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d) *
        cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ)) =
      (2 * ↑Real.pi * Complex.I)⁻¹ •
        ∮ z in C(0, 1 / 2), (1 / (z - 0)) ^ ell • (z - 0)⁻¹ •
          (((center + Complex.log (1 + z)) / (R : ℂ)) ^ d *
            cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ))) := by
    intro d
    unfold rowTest
    rw [cauchyPowerSeries_apply _ 0 (1 / 2) ell 1, smul_mul_assoc]
    congr 1
    rw [mul_comm, ← smul_eq_mul, ← circleIntegral.integral_smul]
    congr 1
    funext z
    simp only [smul_eq_mul]; ring
  simp only [hcomm]
  unfold rowTest
  rw [cauchyPowerSeries_apply _ 0 (1 / 2) ell 1]
  refine HasSum.const_smul _ ?_
  unfold circleIntegral
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun d _ => (1 / 2) * (2 ^ ell * 2) * ((1 / 2) ^ d * D)) (fun d => ?_) (fun d => ?_) ?_ ?_ ?_
  · simp only [deriv_circleMap]
    apply Measurable.aestronglyMeasurable
    fun_prop
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    have hz : ‖circleMap 0 (1 / 2) θ‖ = 1 / 2 := by
      rw [← mem_sphere_zero_iff_norm]; exact circleMap_mem_sphere _ (by norm_num) _
    have hhz := E103TR.h_le center R hR0 hc _ hz
    simp only [deriv_circleMap, sub_zero, smul_eq_mul, norm_mul, norm_pow, norm_div, norm_one,
      norm_inv, hz, Complex.norm_I]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hhz d
    have h2 := E103TR.coeff_le f R hR0 D hfD d
    have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    rw [norm_div] at h3
    norm_num
    norm_num at h3
    have : (0:ℝ) ≤ 2 ^ ell := by positivity
    nlinarith
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    refine Summable.mul_left _ ?_
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    refine HasSum.const_smul _ ?_
    refine HasSum.const_smul _ ?_
    refine HasSum.const_smul _ ?_
    exact hpt _
