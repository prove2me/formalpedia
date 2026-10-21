-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic.hasSum_cauchy_translated_row
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T18:29:06.245987+00:00
-- url     : https://prove2.me/submissions/799f803f-6303-4c6a-b608-b996bc38addf

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers

open scoped BigOperators Topology
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic
open Complex MeasureTheory Filter

/-
Adapted to the attached helper definitions from the analytic row-series argument in
openai/math, revision adc7f1241b42e322a6451854ab7e4b4c146bf78a:
  lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticCollision.lean
  lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticRowSeries.lean
The normalized coefficient is written explicitly, without adding a definition bundle.
-/

private lemma translated_cauchy_coefficient_bound {f : ℂ → ℂ} {R D : ℝ}
    (hR : 0 < R)
    (hfD : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ D) (d : ℕ) :
    ‖cauchyPowerSeries f 0 R d (fun _ => (R : ℂ))‖ ≤ D := by
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ R * (R⁻¹ * D) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
      intro z hz
      have hzR : ‖z‖ = R := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR, norm_inv, hzR, div_self (ne_of_gt hR),
        one_pow, one_mul]
      exact mul_le_mul_of_nonneg_left (hfD z hz) (inv_nonneg.mpr hR.le)
    _ = D := by rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]

private lemma translated_cauchy_pointwise {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R : NNReal} (hR : 0 < R) (z : ℂ) :
    HasSum (fun d => cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ)) *
      (z / (R : ℂ)) ^ d) (f z) := by
  have hr : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  convert! (hf.hasFPowerSeriesOnBall 0 hR).hasSum (y := z) (by simp) using 1
  · funext d
    simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
      Fin.prod_const, smul_eq_mul]
    rw [div_pow]
    field_simp [hr] <;> ring
  · simp

private lemma translated_log_ratio_bound {center t : ℂ} {R : ℝ}
    (hR : 0 < R) (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ht : ‖t‖ ≤ 1 / 2) :
    ‖(center + Complex.log (1 + t)) / (R : ℂ)‖ ≤ 1 / 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  apply (div_le_iff₀ hR).mpr
  have hlog := Complex.norm_log_one_add_half_le_self ht
  have htri := norm_add_le center (Complex.log (1 + t))
  nlinarith

private lemma translated_rowTest_const_mul (ell : ℕ) (c : ℂ) (g : ℂ → ℂ) :
    rowTest ell (fun t => c * g t) = c * rowTest ell g := by
  simp only [rowTest, cauchyPowerSeries_apply, smul_eq_mul]
  have heq : (fun z : ℂ => (1 / (z - 0)) ^ ell * ((z - 0)⁻¹ * (c * g z))) =
      (fun z : ℂ => c * ((1 / (z - 0)) ^ ell * ((z - 0)⁻¹ * g z))) := by
    funext z
    ring
  rw [heq, circleIntegral.integral_const_mul]
  ring

private lemma translated_rowTest_hasSum {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    {bound : ℕ → ℝ}
    (hF : ∀ n, Measurable (F n))
    (hbound : ∀ n z, z ∈ Metric.sphere (0 : ℂ) (1 / 2) → ‖F n z‖ ≤ bound n)
    (hsum : Summable bound)
    (hpoint : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2),
      HasSum (fun n => F n z) (g z)) (ell : ℕ) :
    HasSum (fun n => rowTest ell (F n)) (rowTest ell g) := by
  simp only [rowTest, cauchyPowerSeries_apply]
  apply HasSum.const_smul
  change HasSum (fun n => ∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap 0 (1 / 2)) θ •
        ((1 / (circleMap 0 (1 / 2) θ - 0)) ^ ell •
          (circleMap 0 (1 / 2) θ - 0)⁻¹ • F n (circleMap 0 (1 / 2) θ)))
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap 0 (1 / 2)) θ •
        ((1 / (circleMap 0 (1 / 2) θ - 0)) ^ ell •
          (circleMap 0 (1 / 2) θ - 0)⁻¹ • g (circleMap 0 (1 / 2) θ)))
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => (2 : ℝ) ^ ell * bound n)
  · intro n
    apply Measurable.aestronglyMeasurable
    simp only [deriv_circleMap]
    fun_prop
  · intro n
    apply Eventually.of_forall
    intro θ _
    have hb := hbound n (circleMap 0 (1 / 2) θ)
      (circleMap_mem_sphere 0 (by norm_num) θ)
    simp only [deriv_circleMap, norm_smul, norm_mul, norm_I, mul_one, sub_zero,
      norm_pow, norm_div, norm_one, norm_inv, norm_circleMap_zero]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), one_div,
      inv_div, div_one]
    calc
      _ = (2 : ℝ) ^ ell * ‖F n (circleMap 0 (1 / 2) θ)‖ := by ring
      _ ≤ (2 : ℝ) ^ ell * bound n :=
        mul_le_mul_of_nonneg_left hb (by positivity)
  · exact Eventually.of_forall fun _ _ => hsum.mul_left _
  · simpa only [tsum_mul_left] using
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => (2 : ℝ) ^ ell * ∑' n, bound n) volume 0 (2 * Real.pi))
  · apply Eventually.of_forall
    intro θ _
    exact (((hpoint _ (circleMap_mem_sphere 0 (by norm_num) θ)).const_smul _).const_smul
      _).const_smul _

theorem solution
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (R : NNReal) (hR : 0 < R) (D : ℝ) (hD : 0 ≤ D)
    (hfD : ∀ z ∈ Metric.sphere (0 : ℂ) (R : ℝ), ‖f z‖ ≤ D)
    (center : ℂ) (hc : ‖center‖ + 3 / 4 ≤ (R : ℝ) / 2) (ell : ℕ) :
    HasSum (fun d =>
      rowTest ell (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d) *
        cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ)))
      (rowTest ell (fun t => f (center + Complex.log (1 + t)))) := by
  have hRreal : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have h := translated_rowTest_hasSum
    (F := fun d t => cauchyPowerSeries f 0 (R : ℝ) d (fun _ => (R : ℂ)) *
      ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)
    (g := fun t => f (center + Complex.log (1 + t)))
    (bound := fun d => D * (1 / 2 : ℝ) ^ d)
    (by intro d; fun_prop) ?_ ?_ ?_ ell
  · convert! h using 1
    funext d
    rw [translated_rowTest_const_mul, mul_comm]
  · intro d t ht
    rw [norm_mul, norm_pow]
    apply mul_le_mul (translated_cauchy_coefficient_bound hRreal hfD d)
    · apply pow_le_pow_left₀ (norm_nonneg _)
        (translated_log_ratio_bound hRreal hc _) 
      have htEq : ‖t‖ = (1 / 2 : ℝ) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using ht
      exact htEq.le
    · positivity
    · exact hD
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left D
  · intro t _
    exact translated_cauchy_pointwise hf hR _