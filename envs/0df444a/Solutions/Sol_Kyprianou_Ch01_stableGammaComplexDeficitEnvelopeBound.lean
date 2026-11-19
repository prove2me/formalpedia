-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaComplexDeficitEnvelopeBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:55:18.986148+00:00
-- url     : https://prove2.me/submissions/5203b652-765d-42d8-b79a-e593983e31c1

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_complexExpDeficitTwoNorm
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real
set_option autoImplicit false

/-- Pointwise power envelope for the complex stable Gamma compensated kernel. -/
theorem solution (alpha : ℝ) (w : ℂ) (hwre : w.re ≤ 0)
    (r : ℝ) (hr : 0 < r) :
    ‖(Complex.exp (w * (r : ℂ)) - 1) *
      (((r ^ (-alpha - 1) : ℝ)) : ℂ)‖ ≤
      2 * (if r ≤ 1 then ‖w‖ * r ^ (-alpha)
        else r ^ (-alpha - 1)) := by
  have hp : 0 ≤ r ^ (-alpha - 1) := Real.rpow_nonneg hr.le _
  have hnorm : ‖(((r ^ (-alpha - 1) : ℝ)) : ℂ)‖ =
      r ^ (-alpha - 1) := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  have hrew : r * r ^ (-alpha - 1) = r ^ (-alpha) := by
    calc
      r * r ^ (-alpha - 1) =
        r ^ (1 : ℝ) * r ^ (-alpha - 1) := by rw [Real.rpow_one]
      _ = r ^ (1 + (-alpha - 1)) :=
        (Real.rpow_add hr 1 (-alpha - 1)).symm
      _ = r ^ (-alpha) := by congr 1; ring
  have hre : (w * (r : ℂ)).re ≤ 0 := by
    rw [Complex.re_mul_ofReal]
    exact mul_nonpos_of_nonpos_of_nonneg hwre hr.le
  by_cases hsmall : r ≤ 1
  · have hbound := Kyprianou.Ch01.complexExpDeficitTwoNorm
      (w * (r : ℂ)) hre
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] at hbound
    simp only [if_pos hsmall]
    calc
      ‖(Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (-alpha - 1) : ℝ)) : ℂ)‖ =
        ‖Complex.exp (w * (r : ℂ)) - 1‖ * r ^ (-alpha - 1) := by
          rw [norm_mul, hnorm]
      _ ≤ (2 * (‖w‖ * r)) * r ^ (-alpha - 1) :=
        mul_le_mul_of_nonneg_right hbound hp
      _ = 2 * (‖w‖ * r ^ (-alpha)) := by
        rw [mul_assoc, mul_assoc, hrew]
  · have hexp : ‖Complex.exp (w * (r : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr hre
    have hbound : ‖Complex.exp (w * (r : ℂ)) - 1‖ ≤ 2 := by
      calc
        ‖Complex.exp (w * (r : ℂ)) - 1‖ ≤
            ‖Complex.exp (w * (r : ℂ))‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
        _ ≤ 2 := by simp only [norm_one]; linarith
    simp only [if_neg hsmall]
    calc
      ‖(Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (-alpha - 1) : ℝ)) : ℂ)‖ =
          ‖Complex.exp (w * (r : ℂ)) - 1‖ * r ^ (-alpha - 1) := by
            rw [norm_mul, hnorm]
      _ ≤ 2 * r ^ (-alpha - 1) :=
        mul_le_mul_of_nonneg_right hbound hp
