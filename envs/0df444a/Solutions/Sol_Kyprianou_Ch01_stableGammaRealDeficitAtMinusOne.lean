-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaRealDeficitAtMinusOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:17:26.055531+00:00
-- url     : https://prove2.me/submissions/de1f00f5-b420-449f-92a8-85cb087b262d

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueRealAxis
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real Filter
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1) :
    (∫ x in Set.Ioi (0 : ℝ),
      (Real.exp (-x) - 1) * x ^ (-alpha - 1) ∂volume) =
      Real.Gamma (-alpha) := by
  have h := Kyprianou.Ch01.stableGammaComplexDeficitValueRealAxis
    alpha 1 h0 h1 (by norm_num)
  have heq (x : ℝ) :
      (Complex.exp (-(1 : ℂ) * (x : ℂ)) - 1) *
        ((x ^ (-alpha - 1) : ℝ) : ℂ) =
      (((Real.exp (-x) - 1) * x ^ (-alpha - 1) : ℝ) : ℂ) := by
    have he : -(1 : ℂ) * (x : ℂ) = ((-x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, ← Complex.ofReal_exp]
    push_cast
    ring
  have hc :
      (∫ x in Set.Ioi (0 : ℝ),
        (((Real.exp (-x) - 1) * x ^ (-alpha - 1) : ℝ) : ℂ)
        ∂volume) = ((Real.Gamma (-alpha) : ℝ) : ℂ) := by
    calc
      _ = (∫ x in Set.Ioi (0 : ℝ),
        (Complex.exp (-(1 : ℂ) * (x : ℂ)) - 1) *
          ((x ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact (heq x).symm
      _ = _ := by
        simpa using h
  rw [integral_complex_ofReal] at hc
  exact_mod_cast hc
