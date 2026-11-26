-- Prove2me | solution 1 for MasulloRH.height_two_outer_strip_density_bound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T12:35:48.681501+00:00
-- url     : https://prove2.me/submissions/9bf8f67a-53de-49d0-936c-a79c24131f25

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_HeightTwoWitness
import Theorems.Thm_MasulloRH_theta_norm_le_dyadic_on_tails
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MasulloRH MasulloRH.GaussianApproximation Set

theorem solution (x : ℝ) (hx : x ∈ Icc (-4 : ℝ) 4) (hout : x ≤ -27/8 ∨ 31/8 ≤ x) :
    Real.exp (2*(3/4)*x + 2*(11/48)*|x|) *
      ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖^2 ≤ 1/(2:ℝ)^100 := by
  have hg (i : Fin 11) : -(3:ℝ)/8 ≤ HeightTwoWitness.shifts i ∧
      HeightTwoWitness.shifts i ≤ 19/8 := by
    fin_cases i <;> norm_num [HeightTwoWitness.shifts, HeightTwoWitness.shiftsQ,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
  have hc (i : Fin 11) : ‖HeightTwoWitness.coeffs i‖ ≤ 15 := by
    change ‖((HeightTwoWitness.coeffsQ i : ℝ) : ℂ)‖ ≤ 15
    rw [Complex.norm_real, Real.norm_eq_abs]
    fin_cases i <;> norm_num [HeightTwoWitness.coeffsQ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  have htheta (i : Fin 11) : ‖theta (x - HeightTwoWitness.shifts i)‖ ≤ 1/(2:ℝ)^64 := by
    apply MasulloRH.theta_norm_le_dyadic_on_tails
    rcases hout with h | h
    · left; linarith [(hg i).1]
    · right; linarith [(hg i).2]
  have hsum : ‖∑ i, HeightTwoWitness.coeffs i * theta (x-HeightTwoWitness.shifts i)‖ ≤
      11 * (15 * (1/(2:ℝ)^64)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i : Fin 11, 15 * (1/(2:ℝ)^64) := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]
        exact mul_le_mul (hc i) (htheta i) (norm_nonneg _) (by norm_num)
      _ = _ := by simp
  have hpi : 1 ≤ Real.sqrt Real.pi :=
    (by norm_num : (1:ℝ) ≤ Real.sqrt 1).trans (Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three]))
  have hfac : 3 / Real.sqrt Real.pi ≤ 3 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have he : (2:ℝ)^64 ≤ Real.exp 64 := by
    simpa using (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 64).trans_eq
      (Real.exp_nat_mul 1 64).symm
  have hx2 : 9 ≤ x^2 := by
    rcases hout with h | h
    · nlinarith [sq_nonneg (x+3)]
    · nlinarith [sq_nonneg (x-3)]
  have hdec : Real.exp (-9*x^2) ≤ 1/(2:ℝ)^64 := by
    apply (Real.exp_le_exp.mpr (show -9*x^2 ≤ -64 by linarith)).trans
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) he
  have hp : ‖pulse 2 x‖ ≤ 3 * (1/(2:ℝ)^64) := by
    have hpulse : pulse 2 x = ((3 / Real.sqrt Real.pi * Real.exp (-9*x^2) : ℝ) : ℂ) := by
      unfold pulse
      push_cast
      rw [show (2:ℂ)+1=3 by norm_num, show -((3:ℂ)*(x:ℂ))^2 = -9*(x:ℂ)^2 by ring]
    rw [hpulse, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul hfac hdec (Real.exp_pos _).le (by norm_num)
  have hR : ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖ ≤ 168/(2:ℝ)^64 := by
    apply (norm_sub_le _ _).trans
    linarith [hp, hsum]
  have hxabs : |x| ≤ 4 := abs_le.mpr hx
  have hW : Real.exp (2*(3/4)*x + 2*(11/48)*|x|) ≤ (3:ℝ)^8 := by
    apply (Real.exp_le_exp.mpr (show 2*(3/4)*x + 2*(11/48)*|x| ≤ 8 by linarith [hx.2])).trans
    have h3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    simpa using ((Real.exp_nat_mul 1 8).trans_le (pow_le_pow_left₀ (Real.exp_pos _).le h3 8))
  exact (mul_le_mul hW (pow_le_pow_left₀ (norm_nonneg _) hR 2) (sq_nonneg _)
    (by norm_num)).trans (by norm_num)
