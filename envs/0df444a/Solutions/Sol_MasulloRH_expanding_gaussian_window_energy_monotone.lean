-- Prove2me | solution 1 for MasulloRH.expanding_gaussian_window_energy_monotone
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:26:46.938355+00:00
-- url     : https://prove2.me/submissions/3fd0c51a-f1c1-4c7b-993f-cc5a4bd50ff2

import Definitions.Def_MasulloRH_FixedGaussianTest
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH.FixedGaussianTest MasulloRH.GaussianApproximation MeasureTheory

private theorem ordered_left {j k : ℕ} (h : j ≤ k) : left k ≤ left j := by
  unfold left
  apply add_le_add_right
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact_mod_cast Nat.succ_le_succ h

private theorem wtIntegrable {m : ℕ} (a : Fin m → ℂ) (y : Fin m → ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => Real.exp (2*fullCenter k*x+2*fullWidth k*|x|)*‖residual 0 a y x‖^2) := by
  apply (MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.1
    m 0 (fullCenter k) (fullWidth k) 1 a y (by norm_num) (by norm_num) ?_ ?_).1
  · have e : fullCenter k-fullWidth k=left k := by unfold fullCenter fullWidth;ring
    rw [e]
    unfold left
    positivity
  · have e : fullCenter k+fullWidth k=upper k := by unfold fullCenter fullWidth;ring
    rw [e]
    exact max_lt (by norm_num [right]) (sub_lt_self _ (by positivity))

theorem solution {m : ℕ} (a : Fin m → ℂ) (y : Fin m → ℝ) {j k : ℕ} (h : j ≤ k) :
    energy (fullCenter j) (fullWidth j) (residual 0 a y) ≤ energy (fullCenter k) (fullWidth k) (residual 0 a y) := by
  apply integral_mono (wtIntegrable a y j) (wtIntegrable a y k)
  intro x
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    have cmp : upper j ≤ upper k := by
      apply max_le_max_left
      apply sub_le_sub_left
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ h
    have at_x (i : ℕ) : 2*fullCenter i*x+2*fullWidth i*x=2*(upper i*x) := by
      unfold fullCenter fullWidth
      ring
    rw [at_x,at_x]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right cmp hx) (by norm_num)
  · rw [abs_of_nonpos hx]
    have at_x (i : ℕ) : 2*fullCenter i*x+2*fullWidth i*(-x)=2*(left i*x) := by
      unfold fullCenter fullWidth
      ring
    rw [at_x,at_x]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonpos_right (ordered_left h) hx) (by norm_num)
