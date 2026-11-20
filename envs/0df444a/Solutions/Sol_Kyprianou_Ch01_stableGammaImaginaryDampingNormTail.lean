-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaImaginaryDampingNormTail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:17:07.408923+00:00
-- url     : https://prove2.me/submissions/1a6870b2-fc81-4892-b10f-89b017dab34c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

/-- Uniform contraction on the positive damped-imaginary Fourier tail. -/
theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re = 0) (epsilon x : ℝ)
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (hx : 0 < x)
    (hx1 : 1 < x) :
    ‖(Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1) *
        (((x ^ (-alpha - 1) : ℝ)) : ℂ)‖ ≤
      (‖w‖ + 2) * x ^ (-alpha - 1) := by
  have hre : ((w - (epsilon : ℂ)) * (x : ℂ)).re =
      -epsilon * x := by
    simp [Complex.mul_re, Complex.sub_re, hwre]
  have hnonpos : -epsilon * x ≤ 0 := by
    nlinarith [mul_nonneg he0 hx.le]
  have hnorm : ‖Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, hre]
    exact Real.exp_le_one_iff.mpr hnonpos
  have hkernel : ‖Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1‖ ≤ 2 := by
    calc
      ‖Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1‖ ≤
          ‖Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ))‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ 1 + 1 := by simpa using add_le_add hnorm (le_refl (1 : ℝ))
      _ = 2 := by ring
  have hpower : 0 ≤ x ^ (-alpha - 1) := Real.rpow_nonneg hx.le _
  have hcoeff : 2 ≤ ‖w‖ + 2 := by
    nlinarith [norm_nonneg w]
  calc
    ‖(Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1) *
        (((x ^ (-alpha - 1) : ℝ)) : ℂ)‖ =
          ‖Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1‖ *
            x ^ (-alpha - 1) := by
      rw [norm_mul]
      simp [Complex.norm_real, abs_of_nonneg hpower]
    _ ≤ 2 * x ^ (-alpha - 1) :=
      mul_le_mul_of_nonneg_right hkernel hpower
    _ ≤ (‖w‖ + 2) * x ^ (-alpha - 1) :=
      mul_le_mul_of_nonneg_right hcoeff hpower
