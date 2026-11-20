-- Prove2me | solution 1 for Kyprianou.Ch01.complexPureImaginaryExponentialLipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:11:50.788449+00:00
-- url     : https://prove2.me/submissions/3457b2d2-9174-4482-8a91-e5d402e18748

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real
set_option autoImplicit false

/-- Pure imaginary exponential is Lipschitz with respect to its real argument. -/
theorem solution
    (w : ℂ) (hwre : w.re = 0) (x : ℝ) (hx : 0 ≤ x) :
    ‖Complex.exp (w * (x : ℂ)) - 1‖ ≤ ‖w‖ * x := by
  have hw : w = Complex.I * (w.im : ℂ) := by
    apply Complex.ext
    · simp [hwre]
    · simp
  have harg : w * (x : ℂ) = Complex.I * ((w.im * x : ℝ) : ℂ) := by
    conv_lhs => rw [hw]
    push_cast
    ring
  have hnorm : ‖w‖ = |w.im| := by
    calc
      ‖w‖ = ‖Complex.I * (w.im : ℂ)‖ := by
        conv_lhs => rw [hw]
      _ = |w.im| := by simp [norm_mul]
  have hbound :
      ‖Complex.exp (Complex.I * ((w.im * x : ℝ) : ℂ)) - 1‖ ≤
        |w.im * x| := by
    simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := w.im * x)
  calc
    ‖Complex.exp (w * (x : ℂ)) - 1‖ =
        ‖Complex.exp (Complex.I * ((w.im * x : ℝ) : ℂ)) - 1‖ := by
          rw [harg]
    _ ≤ |w.im * x| := hbound
    _ = ‖w‖ * x := by
      rw [abs_mul, abs_of_nonneg hx, hnorm]
