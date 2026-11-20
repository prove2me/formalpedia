-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftMellinIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:22:28.002754+00:00
-- url     : https://prove2.me/submissions/bf331d47-04d7-4dda-8e6c-907e8779b58a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

/-- Complex exponential Mellin integrability from a real Gamma-envelope theorem. -/
theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    IntegrableOn
      (fun r : ℝ => Complex.exp (w * (r : ℂ)) *
        ((r ^ (-alpha) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have hb : 0 < -w.re := by linarith
  have hs : (-1 : ℝ) < -alpha := by linarith
  have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := -alpha) (b := -w.re)
    hs (by norm_num) hb
  apply Integrable.mono hreal (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hp : 0 < r ^ (-alpha) := Real.rpow_pos_of_pos hr _
  have hre : (w * (r : ℂ)).re = w.re * r := by simp
  simp [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp, hre, Real.rpow_one]
  exact le_of_eq (mul_comm _ _)
