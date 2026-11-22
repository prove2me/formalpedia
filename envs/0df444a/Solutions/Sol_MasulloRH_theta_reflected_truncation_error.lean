-- Prove2me | solution 1 for MasulloRH.theta_reflected_truncation_error
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T16:03:34.282893+00:00
-- url     : https://prove2.me/submissions/98236387-1d0e-4745-ae77-94802bfc4143

import Definitions.Def_MasulloRH_GaussianThetaTruncation
import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Theorems.Thm_MasulloRH_theta_reflection
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace MasulloRH.ReflectedApprox

theorem gaussian_parameter_lower (x : ℝ) (hx : -1 ≤ x) :
    (1 / 3 : ℝ) ≤ Real.pi * (Real.exp x) ^ 2 := by
  have he : (1 / 3 : ℝ) ≤ Real.exp x := by
    have hrec : (1 / 3 : ℝ) ≤ (Real.exp 1)⁻¹ := by
      rw [← one_div (Real.exp 1)]
      apply (le_div_iff₀ (Real.exp_pos _)).2
      nlinarith [Real.exp_one_lt_three]
    exact hrec.trans (by simpa only [Real.exp_neg] using Real.exp_le_exp.mpr hx)
  have hs : (1 / 9 : ℝ) ≤ (Real.exp x) ^ 2 := by nlinarith
  have hp := Real.pi_gt_three.le
  nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg (Real.exp x))]

theorem reflected_parameter_lower (x : ℝ) (hx : x ≤ -1) :
    (1 / 3 : ℝ) ≤ Real.pi * (Real.exp (-x - Real.log 4)) ^ 2 := by
  have he : (2 : ℝ) ≤ Real.exp (-x) := by
    have h := Real.add_one_le_exp (-x)
    linarith
  have hexp : Real.exp (-x - Real.log 4) = Real.exp (-x) / 4 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [hexp]
  have hs : (1 / 4 : ℝ) ≤ (Real.exp (-x) / 4) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le
    (sq_nonneg (Real.exp (-x) / 4))]

/-- A rational lower bound for the Gaussian parameter gives a simple common
tail allowance, uniform over every evaluation on either side of the cutoff. -/
theorem gaussian_tail_bound_le (a : ℝ) (ha : (1 / 3 : ℝ) ≤ a) (K : ℕ) :
    12 * Real.exp (-a * ((K : ℝ) + 1) ^ 2) /
        (1 - Real.exp (-a * (2 * (K : ℝ) + 3))) ≤
      24 * Real.exp (-((K : ℝ) + 1) ^ 2 / 3) := by
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hap : 0 ≤ a := by linarith
  have ht : 1 ≤ a * (2 * (K : ℝ) + 3) := by
    nlinarith [mul_nonneg hap hk]
  have he : (2 : ℝ) ≤ Real.exp (a * (2 * (K : ℝ) + 3)) := by
    linarith [Real.add_one_le_exp (a * (2 * (K : ℝ) + 3))]
  have hneg : Real.exp (-a * (2 * (K : ℝ) + 3)) ≤ (1 / 2 : ℝ) := by
    rw [neg_mul, Real.exp_neg]
    rw [← one_div (Real.exp (a * (2 * (K : ℝ) + 3)))]
    exact (div_le_iff₀ (Real.exp_pos _)).2 (by nlinarith)
  have hd : (1 / 2 : ℝ) ≤ 1 - Real.exp (-a * (2 * (K : ℝ) + 3)) := by linarith
  have hn : Real.exp (-a * ((K : ℝ) + 1) ^ 2) ≤
      Real.exp (-((K : ℝ) + 1) ^ 2 / 3) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right ha (sq_nonneg ((K : ℝ) + 1))]
  apply (div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-a * (2 * (K : ℝ) + 3)))).2
  have h := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 24 * Real.exp (-((K : ℝ) + 1) ^ 2 / 3) by positivity)
  nlinarith


end MasulloRH.ReflectedApprox


set_option autoImplicit false
open MasulloRH.GaussianApproximation
open MasulloRH.ReflectedApprox

private theorem theta_partial_error_of_parameter (K : ℕ) (x : ℝ)
    (hx : (1 / 3 : ℝ) ≤ Real.pi * (Real.exp x) ^ 2) :
    ‖theta x - thetaPartial K x‖ ≤
      24 * Real.exp (-((K : ℝ) + 1) ^ 2 / 3) := by
  have h := MasulloRH.theta_gaussian_truncation_error x K
  change ‖theta x - thetaPartial K x‖ ≤ _ at h
  have hB := gaussian_tail_bound_le (Real.pi * (Real.exp x) ^ 2) hx K
  have hn (t : ℝ) : -(Real.pi * (Real.exp x) ^ 2) * t =
      -Real.pi * (Real.exp x) ^ 2 * t := by ring
  simp only [hn] at hB
  exact h.trans hB

/-- A finite reflected evaluation with a common Gaussian error allowance.
The cutoff -1 is rational, so shifted integration cells can use rational endpoints. -/
theorem solution (K : ℕ) (x : ℝ) :
    ‖theta x - thetaPartialReflected K x‖ ≤
      (24 * Real.exp (-((K : ℝ) + 1) ^ 2 / 3)) *
        max 1 (Real.exp (-x) / 2) := by
  unfold thetaPartialReflected
  split_ifs with hx
  · exact (theta_partial_error_of_parameter K x (gaussian_parameter_lower x hx)).trans
      (le_mul_of_one_le_right (by positivity) (le_max_left _ _))
  · rw [MasulloRH.theta_reflection x, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h := theta_partial_error_of_parameter K (-x - Real.log 4)
      (reflected_parameter_lower x (le_of_not_ge hx))
    calc
      _ ≤ (Real.exp (-x) / 2) *
          (24 * Real.exp (-((K : ℝ) + 1) ^ 2 / 3)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = (24 * Real.exp (-((K : ℝ) + 1) ^ 2 / 3)) * (Real.exp (-x) / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

