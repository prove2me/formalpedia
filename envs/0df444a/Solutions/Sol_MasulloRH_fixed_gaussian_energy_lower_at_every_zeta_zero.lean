-- Prove2me | solution 1 for MasulloRH.fixed_gaussian_energy_lower_at_every_zeta_zero
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:25:14.217154+00:00
-- url     : https://prove2.me/submissions/cb832145-f3d4-49ca-b584-f36d57d737b6

import Theorems.Thm_MasulloRH_fixed_gaussian_residual_laplace_at_zeta_zero
import Theorems.Thm_MasulloRH_exact_laplace_energy_bound_on_window
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open MeasureTheory MasulloRH.GaussianApproximation

/-- Every zero strictly within the window gives a positive lower bound on the
unit-width Gaussian error, with its full ordinate dependence. -/
theorem solution (c b : ℝ) (hc : 0<c-b) (hc' : c+b<1) {m : ℕ} (a : Fin m → ℂ)
    (y : Fin m → ℝ) (s : ℂ) (hs : |s.re-c|<b) (hz : riemannZeta s=0) :
    Real.exp ((s.re^2-s.im^2)/2) * ((b^2-(s.re-c)^2)/b) ≤
      energy c b (residual 0 a y) := by
  let d := s.re-c
  have hm : 0<b-d := sub_pos.mpr (abs_lt.mp hs).2
  have hp : 0<b+d := by dsimp only [d];linarith [(abs_lt.mp hs).1]
  have hb : 0<b := (abs_nonneg _).trans_lt hs
  have hd : 0<b^2-d^2 := by nlinarith [mul_pos hm hp]
  have hzero := MasulloRH.fixed_gaussian_residual_laplace_at_zeta_zero a y s
    (by linarith [(abs_lt.mp hs).1]) (by linarith [(abs_lt.mp hs).2]) hz
  have hi := (MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.1
    m 0 c b 1 a y (by norm_num) (by norm_num) hc hc').1
  have h := MasulloRH.exact_laplace_energy_bound_on_window (residual 0 a y) c b s hs hi
  rw [hzero.2] at h
  have hv : ‖Complex.exp (s^2/4)‖^2=Real.exp ((s.re^2-s.im^2)/2) := by
    rw [Complex.norm_exp,←Real.exp_nat_mul]
    congr 1
    norm_num [pow_two,Complex.div_re,Complex.mul_re]
    ring
  rw [hv] at h
  have cancel : (1/(2*(b-d))+1/(2*(b+d)))*((b^2-d^2)/b)=1 := by
    field_simp [hm.ne',hp.ne',hb.ne']
    ring
  have hh := mul_le_mul_of_nonneg_right h (div_nonneg hd.le hb.le)
  simpa only [mul_assoc,cancel,mul_one,d] using hh
