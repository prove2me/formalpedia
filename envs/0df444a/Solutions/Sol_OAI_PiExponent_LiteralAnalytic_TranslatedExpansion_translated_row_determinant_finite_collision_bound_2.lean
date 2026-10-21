-- Prove2me | solution 2 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.translated_row_determinant_finite_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:15:13.93179+00:00
-- url     : https://prove2.me/submissions/946bf72f-b0c1-4c16-afe7-295b9479e6cb

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Theorems.Thm_OAI_PiExponent_Collision_infinite_tested_series_collision_bound
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_CollisionAnalytic_hasSum_cauchy_translated_row

open scoped BigOperators Topology
open Complex
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

namespace CollAux

theorem norm_normalizedTaylorCoeff_le {f : ℂ → ℂ} {R D : ℝ} (hR : 0 < R)
    (hD : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ D) (d : ℕ) :
    ‖cauchyPowerSeries f 0 R d (fun _ => (R : ℂ))‖ ≤ D := by
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ R * (R⁻¹ * D) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
      intro z hz
      have hzR : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR, norm_inv, hzR, div_self (ne_of_gt hR),
        one_pow, one_mul]
      exact mul_le_mul_of_nonneg_left (hD z hz) (inv_nonneg.mpr hR.le)
    _ = D := by field_simp

theorem norm_rowTest_le {f : ℂ → ℂ} {D : ℝ}
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
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD z hz) (by norm_num))
        (by positivity)
    _ = _ := by ring

theorem norm_shifted_log_div_le_half {center t : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ht : ‖t‖ ≤ 1 / 2) :
    ‖(center + Complex.log (1 + t)) / (R : ℂ)‖ ≤ 1 / 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  apply (div_le_iff₀ hR).mpr
  have hlog := Complex.norm_log_one_add_half_le_self ht
  have htri := norm_add_le center (Complex.log (1 + t))
  nlinarith

theorem norm_rowTest_shifted_power_le {center : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ell d : ℕ) :
    ‖rowTest ell (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)‖ ≤
      (2 : ℝ) ^ ell * (1 / 2 : ℝ) ^ d := by
  apply norm_rowTest_le
  intro t ht
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) (norm_shifted_log_div_le_half hR hc _)
  simpa only [Metric.mem_sphere, dist_zero_right] using ht.le

theorem collisionRatio_pos : 0 < OAI.PiExponent.Collision.collisionRatio :=
  Real.exp_pos _

theorem collisionRatio_lt_one : OAI.PiExponent.Collision.collisionRatio < 1 := by
  unfold OAI.PiExponent.Collision.collisionRatio
  rw [show -(Real.log 2) / 2 = -(Real.log 2 / 2) by ring]
  rw [show (1 : ℝ) = Real.exp 0 by simp]
  apply Real.exp_lt_exp.mpr
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

theorem collisionRatio_mul_self :
    OAI.PiExponent.Collision.collisionRatio * OAI.PiExponent.Collision.collisionRatio = 1 / 2 := by
  unfold OAI.PiExponent.Collision.collisionRatio
  rw [← Real.exp_add]
  have h : -(Real.log 2) / 2 + -(Real.log 2) / 2 = -Real.log 2 := by ring
  rw [h, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

end CollAux

/-- Finite collision bound for translated row determinants. -/
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
      (((Fintype.card ι).factorial : ℝ) * Real.exp (H * budgetCoeff) ^ Fintype.card ι *
        (2 : ℝ) ^ (∑ r, ell r)) *
        OAI.PiExponent.Collision.collisionRatio ^
          (∑ A : κ, (((Finset.univ : Finset ι).filter
            (fun r => group r = A)).card.choose 2)) *
        ((1 - OAI.PiExponent.Collision.collisionRatio)⁻¹) ^ Fintype.card ι := by
  classical
  let B : ι → ℕ → ℂ := fun i d => rowTest (ell i)
    (fun t => ((center i + Complex.log (1 + t)) / (R : ℂ)) ^ d)
  let C : κ → ℕ → ι → ℂ := fun a d j =>
    cauchyPowerSeries (f a j) 0 (R : ℝ) d (fun _ => (R : ℂ))
  have hratio := CollAux.collisionRatio_mul_self
  have hmain := OAI.PiExponent.Collision.infinite_tested_series_collision_bound
    group B C (Real.exp (H * budgetCoeff)) OAI.PiExponent.Collision.collisionRatio
    (fun i => (2 : ℝ) ^ (ell i))
    (Real.exp_pos _).le CollAux.collisionRatio_pos.le
    CollAux.collisionRatio_lt_one (fun _ => by positivity)
    (fun A d c => CollAux.norm_normalizedTaylorCoeff_le (by exact_mod_cast hR)
      (fun z hz => hfD A c z hz) d)
    (fun i d => by
      dsimp only [B]
      rw [hratio]
      exact CollAux.norm_rowTest_shifted_power_le (by exact_mod_cast hR) (hc i) (ell i) d)
    (T := fun r c => rowTest (ell r) (fun t => f (group r) c (center r + Complex.log (1 + t))))
    (fun r c =>
      OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic.hasSum_cauchy_translated_row
        (hf (group r) c) R hR (Real.exp (H * budgetCoeff)) (Real.exp_pos _).le
        (hfD (group r) c) (center r) (hc r) (ell r))
  have hprod : (∏ i : ι, (2 : ℝ) ^ (ell i)) = (2 : ℝ) ^ (∑ i, ell i) := by
    rw [Finset.prod_pow_eq_pow_sum]
  simpa only [B, C, hprod] using hmain
