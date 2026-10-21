-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.translated_row_determinant_finite_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T18:08:00.825997+00:00
-- url     : https://prove2.me/submissions/88f25368-94d2-4878-8ac2-233965736fb1

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_CollisionAnalytic_hasSum_cauchy_translated_row
import Theorems.Thm_OAI_PiExponent_Collision_infinite_tested_series_collision_bound
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open scoped BigOperators Topology
open OAI.PiExponent
open OAI.PiExponent.Collision
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

private theorem norm_scaled_cauchy_coefficient_le
    {f : ℂ → ℂ} {R D : ℝ} (hR : 0 < R)
    (hD : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ D) (d : ℕ) :
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
      exact mul_le_mul_of_nonneg_left (hD z hz) (inv_nonneg.mpr hR.le)
    _ = D := by field_simp [ne_of_gt hR]

private theorem norm_row_test_le
    {f : ℂ → ℂ} {D : ℝ}
    (hD : ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2), ‖f t‖ ≤ D) (ell : ℕ) :
    ‖rowTest ell f‖ ≤ (2 : ℝ) ^ ell * D := by
  unfold rowTest
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ (1 / 2 : ℝ) * (2 ^ ell * (2 * D)) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by norm_num)
      intro z hz
      have hzR : ‖z‖ = (1 / 2 : ℝ) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, norm_one, norm_inv, hzR]
      norm_num only [one_div, inv_div, div_one]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hD z hz) (by norm_num)) (by positivity)
    _ = _ := by ring

private theorem norm_shifted_log_ratio_le
    {center t : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ht : ‖t‖ ≤ 1 / 2) :
    ‖(center + Complex.log (1 + t)) / (R : ℂ)‖ ≤ 1 / 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  apply (div_le_iff₀ hR).mpr
  have hlog := Complex.norm_log_one_add_half_le_self ht
  have htri := norm_add_le center (Complex.log (1 + t))
  nlinarith

private theorem norm_shifted_power_row_test_le
    {center : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ell d : ℕ) :
    ‖rowTest ell (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)‖ ≤
      (2 : ℝ) ^ ell * (1 / 2 : ℝ) ^ d := by
  apply norm_row_test_le
  intro t ht
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) (norm_shifted_log_ratio_le hR hc _)
  simpa only [Metric.mem_sphere, dist_zero_right] using ht.le

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) {H budgetCoeff : ℝ}
    (hf : ∀ A c, Differentiable ℂ (f A c))
    (hfD : ∀ A c z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) →
      ‖f A c z‖ ≤ Real.exp (H * budgetCoeff))
    (hc : ∀ r, ‖center r‖ + 3 / 4 ≤ (R : ℝ) / 2) :
    ‖Matrix.det (fun r c => rowTest (ell r)
      (fun t => f (group r) c (center r + Complex.log (1 + t))))‖ ≤
      (((Fintype.card ι).factorial : ℝ) *
        Real.exp (H * budgetCoeff) ^ Fintype.card ι *
        (2 : ℝ) ^ (∑ r, ell r)) *
        Collision.collisionRatio ^
          (∑ A : κ, (((Finset.univ : Finset ι).filter
            (fun r => group r = A)).card.choose 2)) *
        ((1 - Collision.collisionRatio)⁻¹) ^ Fintype.card ι := by
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hs0 : 0 ≤ Collision.collisionRatio := (Real.exp_pos _).le
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hneg : -Real.log 2 / 2 < 0 := by linarith
  have hs1 : Collision.collisionRatio < 1 := by
    unfold Collision.collisionRatio
    exact Real.exp_lt_one_iff.mpr hneg
  have hss : Collision.collisionRatio * Collision.collisionRatio = 1 / 2 := by
    calc
      Collision.collisionRatio * Collision.collisionRatio =
          Real.exp ((-Real.log 2 / 2) + (-Real.log 2 / 2)) := by
            unfold Collision.collisionRatio
            exact (Real.exp_add _ _).symm
      _ = Real.exp (-Real.log 2) := by congr 1 <;> ring
      _ = (Real.exp (Real.log 2))⁻¹ := by rw [Real.exp_neg]
      _ = (2 : ℝ)⁻¹ := by rw [Real.exp_log (by norm_num)]
      _ = 1 / 2 := by norm_num
  let B : ι → ℕ → ℂ := fun r d => rowTest (ell r)
    (fun t => ((center r + Complex.log (1 + t)) / (R : ℂ)) ^ d)
  let C : κ → ℕ → ι → ℂ := fun A d c =>
    cauchyPowerSeries (f A c) 0 (R : ℝ) d (fun _ => (R : ℂ))
  let T : Matrix ι ι ℂ := fun r c => rowTest (ell r)
    (fun t => f (group r) c (center r + Complex.log (1 + t)))
  have hC : ∀ A d c, ‖C A d c‖ ≤ Real.exp (H * budgetCoeff) := by
    intro A d c
    exact norm_scaled_cauchy_coefficient_le hRreal (hfD A c) d
  have hB : ∀ r d, ‖B r d‖ ≤ (2 : ℝ) ^ ell r *
      (Collision.collisionRatio * Collision.collisionRatio) ^ d := by
    intro r d
    rw [hss]
    exact norm_shifted_power_row_test_le hRreal (hc r) (ell r) d
  have hsum : ∀ r c, HasSum (fun d => B r d * C (group r) d c) (T r c) := by
    intro r c
    exact hasSum_cauchy_translated_row (hf (group r) c) R hR
      (Real.exp (H * budgetCoeff)) (Real.exp_pos _).le (hfD (group r) c)
      (center r) (hc r) (ell r)
  have hbound := Collision.infinite_tested_series_collision_bound
    group B C (Real.exp (H * budgetCoeff)) Collision.collisionRatio
    (fun r => (2 : ℝ) ^ ell r) (Real.exp_pos _).le hs0 hs1
    (fun _ => by positivity) hC hB T hsum
  simpa only [T, Finset.prod_pow_eq_pow_sum] using hbound
