-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaImaginaryDampingNormNearZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:15:52.674839+00:00
-- url     : https://prove2.me/submissions/8386fec6-ba6b-40d1-89be-eeb37101670c

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaDampedExpLinearBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

/-- Near-zero exact Gamma kernel is dominated by the integrable stable power. -/
theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re = 0) (epsilon x : ℝ)
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (hx : 0 < x)
    (hx1 : x ≤ 1) :
    ‖(Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1) *
        (((x ^ (-alpha - 1) : ℝ)) : ℂ)‖ ≤
      (‖w‖ + 2) * x ^ (-alpha) := by
  have hlin :=
    Kyprianou.Ch01.stableGammaDampedExpLinearBound
      w hwre epsilon x he0 he1 hx hx1
  have hpow : 0 ≤ x ^ (-alpha - 1) :=
    Real.rpow_nonneg hx.le _
  have hmul : x * x ^ (-alpha - 1) = x ^ (-alpha) := by
    calc
      x * x ^ (-alpha - 1) =
          x ^ (1 : ℝ) * x ^ (-alpha - 1) := by rw [Real.rpow_one]
      _ = x ^ (1 + (-alpha - 1)) :=
          (Real.rpow_add hx _ _).symm
      _ = x ^ (-alpha) := by congr 1; ring
  calc
    ‖(Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1) *
        (((x ^ (-alpha - 1) : ℝ)) : ℂ)‖ =
        ‖Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1‖ *
          x ^ (-alpha - 1) := by
      rw [norm_mul]
      simp [Complex.norm_real, abs_of_nonneg hpow]
    _ ≤ ((‖w‖ + 2) * x) * x ^ (-alpha - 1) :=
      mul_le_mul_of_nonneg_right hlin hpow
    _ = (‖w‖ + 2) * x ^ (-alpha) := by
      rw [mul_assoc, hmul]
