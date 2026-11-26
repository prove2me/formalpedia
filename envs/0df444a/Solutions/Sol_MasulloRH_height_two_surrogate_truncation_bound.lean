-- Prove2me | solution 1 for MasulloRH.height_two_surrogate_truncation_bound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T12:35:47.039818+00:00
-- url     : https://prove2.me/submissions/d732743c-e77c-497b-b2e2-9bef8ad070a0

import Definitions.Def_MasulloRH_HeightTwoCurvature
import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Theorems.Thm_MasulloRH_theta_reflection
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MasulloRH MasulloRH.GaussianApproximation MasulloRH.HeightTwoCurvature

private theorem single_error (b : Bool) (z : ℝ) :
    ‖theta z - (thetaSix b z : ℂ)‖ ≤ thetaTail b z := by
  let y := arg b z
  let S (x : ℝ) : ℝ := 2 * ∑ k ∈ Finset.range 6,
    let t := ((k : ℝ) + 1) * Real.exp x
    Real.exp (-Real.pi*t^2) - 3*Real.exp (-Real.pi*(2*t)^2) + 2*Real.exp (-Real.pi*(4*t)^2)
  have h := MasulloRH.theta_gaussian_truncation_error y 6
  have h' : ‖theta y - (S y : ℂ)‖ ≤
      12 * Real.exp (-Real.pi * (Real.exp y)^2 * 49) /
        (1 - Real.exp (-Real.pi * (Real.exp y)^2 * 15)) := by
    simpa only [S, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum,
      Nat.cast_ofNat, show (6 + 1 : ℝ)^2 = 49 by norm_num,
      show (2*6+3 : ℝ) = 15 by norm_num] using h
  have heq : theta z = (factor b z : ℂ) * theta y := by
    cases b
    · simp [factor, y, arg]
    · exact MasulloRH.theta_reflection z
  have hp : 0 ≤ factor b z := by
    cases b
    · exact zero_le_one
    · exact div_nonneg (Real.exp_pos _).le (by norm_num)
  change ‖theta z - ((factor b z * S y : ℝ) : ℂ)‖ ≤ _
  rw [heq, Complex.ofReal_mul, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_left h' hp

theorem solution (j : ℕ) (x : ℝ) :
    ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x - (surrogate j x : ℂ)‖ ≤
      tail j x := by
  have hp : pulse 2 x = ((3 / Real.sqrt Real.pi * Real.exp (-9*x^2) : ℝ) : ℂ) := by
    rw [pulse, Complex.ofReal_mul (3 / Real.sqrt Real.pi) (Real.exp (-9*x^2)), Complex.ofReal_exp]
    push_cast
    congr 1 <;> congr 1 <;> ring
  let c (i : Fin 11) : ℂ := ((HeightTwoWitness.coeffsQ i : ℝ) : ℂ)
  let z (i : Fin 11) := x - HeightTwoWitness.shifts i
  have he : residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x - (surrogate j x : ℂ) =
      -(∑ i, c i * (theta (z i) - (thetaSix (reflected j i) (z i) : ℂ))) := by
    simp only [GaussianApproximation.residual, surrogate, hp, Complex.ofReal_sub, Complex.ofReal_sum,
      Complex.ofReal_mul, mul_sub, Finset.sum_sub_distrib, c, z, HeightTwoWitness.coeffs,
      Complex.ofReal_ratCast]
    abel
  rw [he, norm_neg]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, show ‖c i‖ = |(HeightTwoWitness.coeffsQ i : ℝ)| by
    exact (Complex.norm_real _).trans (Real.norm_eq_abs _)]
  exact mul_le_mul_of_nonneg_left (single_error _ _) (abs_nonneg _)
