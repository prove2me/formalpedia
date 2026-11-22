-- Prove2me | solution 1 for MasulloRH.theta_reflection
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T15:54:50.476484+00:00
-- url     : https://prove2.me/submissions/b67ba27d-e18b-4b32-a76b-bab9bcc38c1d

import Mathlib
import Definitions.Def_MasulloRH_GaussianThetaApproximation

/- Exact reflection of the published dyadic Gaussian theta definition.
Uses Mathlib's Real.tsum_exp_neg_mul_int_sq (Gaussian Poisson summation).
The summability, dyadic regrouping, scaling factors, and logarithmic substitution
are proved below; no RH/Mertens hypothesis or mission theorem is imported. -/

open scoped BigOperators
set_option autoImplicit false

namespace MasulloRH.ThetaReflectionCore

noncomputable def gaussian (t : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-Real.pi * ((k : ℝ) * t) ^ 2)

noncomputable def dyadic (t : ℝ) : ℝ :=
  ∑' k : ℤ, (Real.exp (-Real.pi * ((k : ℝ) * t) ^ 2) -
    3 * Real.exp (-Real.pi * (2 * ((k : ℝ) * t)) ^ 2) +
    2 * Real.exp (-Real.pi * (4 * ((k : ℝ) * t)) ^ 2))

lemma gaussian_summable (t : ℝ) (ht : 0 < t) :
    Summable (fun k : ℤ => Real.exp (-Real.pi * ((k : ℝ) * t) ^ 2)) := by
  have hn : Summable (fun n : ℕ => Real.exp ((-Real.pi * t ^ 2) * (n : ℝ) ^ 2)) := by
    apply Real.summable_exp_nat_mul_of_ge
      (mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) (sq_pos_of_pos ht))
    intro n
    have h : (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by exact_mod_cast Nat.le_mul_self n
    nlinarith
  have hnat : Summable (fun n : ℕ => Real.exp (-Real.pi * ((n : ℝ) * t) ^ 2)) := by
    convert hn using 1
    funext n
    congr 1
    ring
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast] using hnat
  · simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, neg_sq] using hnat

lemma gaussian_inversion (t : ℝ) (ht : 0 < t) :
    gaussian t = (1 / t) * gaussian (1 / t) := by
  have h := Real.tsum_exp_neg_mul_int_sq (a := t ^ 2) (sq_pos_of_pos ht)
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq ht.le] at h
  calc
    gaussian t = ∑' k : ℤ, Real.exp (-Real.pi * t ^ 2 * (k : ℝ) ^ 2) := by
      apply tsum_congr
      intro k
      congr 1
      ring
    _ = (1 / t) * ∑' k : ℤ, Real.exp (-Real.pi / t ^ 2 * (k : ℝ) ^ 2) := h
    _ = (1 / t) * gaussian (1 / t) := by
      congr 1
      apply tsum_congr
      intro k
      congr 1
      field_simp

lemma dyadic_eq (t : ℝ) (ht : 0 < t) :
    dyadic t = gaussian t - 3 * gaussian (2 * t) + 2 * gaussian (4 * t) := by
  have h₁ := gaussian_summable t ht
  have h₂ := gaussian_summable (2 * t) (by positivity)
  have h₄ := gaussian_summable (4 * t) (by positivity)
  have he₂ (k : ℤ) : 2 * ((k : ℝ) * t) = (k : ℝ) * (2 * t) := by ring
  have he₄ (k : ℤ) : 4 * ((k : ℝ) * t) = (k : ℝ) * (4 * t) := by ring
  simp only [dyadic, gaussian, he₂, he₄]
  rw [(h₁.sub (h₂.mul_left 3)).tsum_add (h₄.mul_left 2),
    h₁.tsum_sub (h₂.mul_left 3), tsum_mul_left, tsum_mul_left]

lemma dyadic_inversion (t : ℝ) (ht : 0 < t) :
    dyadic t = (1 / (2 * t)) * dyadic (1 / (4 * t)) := by
  rw [dyadic_eq t ht, dyadic_eq (1 / (4 * t)) (by positivity)]
  rw [gaussian_inversion t ht, gaussian_inversion (2 * t) (by positivity),
    gaussian_inversion (4 * t) (by positivity)]
  have he₂ : 2 * (1 / (4 * t)) = 1 / (2 * t) := by field_simp; ring
  have he₄ : 4 * (1 / (4 * t)) = 1 / t := by field_simp
  rw [he₂, he₄]
  field_simp
  ring

/-- The dyadic combination is a scaled eigenfunction of the Gaussian Poisson transformation. -/
theorem dyadic_log_reflection (x : ℝ) :
    dyadic (Real.exp x) = (Real.exp (-x) / 2) *
      dyadic (Real.exp (-x - Real.log 4)) := by
  have he : Real.exp (-x - Real.log 4) = 1 / (4 * Real.exp x) := by
    rw [Real.exp_sub, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    ring
  rw [he, dyadic_inversion (Real.exp x) (Real.exp_pos x), Real.exp_neg]
  ring

end MasulloRH.ThetaReflectionCore


open MasulloRH.GaussianApproximation

private lemma theta_eq_dyadic (x : ℝ) :
    theta x = (MasulloRH.ThetaReflectionCore.dyadic (Real.exp x) : ℂ) := by
  simp only [theta, MasulloRH.ThetaReflectionCore.dyadic, Complex.ofReal_tsum]

theorem solution (x : ℝ) :
    theta x = ((Real.exp (-x) / 2 : ℝ) : ℂ) * theta (-x - Real.log 4) := by
  rw [theta_eq_dyadic, theta_eq_dyadic]
  exact_mod_cast MasulloRH.ThetaReflectionCore.dyadic_log_reflection x
