-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaComplexDeficitValueRealAxis
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:07:34.107179+00:00
-- url     : https://prove2.me/submissions/3cd86c6f-0dab-408d-a1f8-8a9fce53358e

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

/-- Real-axis complex stable gamma formula from the proven real Laplace-Gamma integral. -/
theorem solution
    (alpha u : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (hu : 0 < u) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (-(u : ℂ) * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (u : ℂ)) := by
  have hreal := (Kyprianou.Ch01.stableGammaIntegral
    alpha u h0 h1 hu).2
  have hfun (r : ℝ) :
      (Complex.exp (-(u : ℂ) * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) =
      (((Real.exp (-(u * r)) - 1) * r ^ (-alpha - 1) : ℝ) : ℂ) := by
    have harg : -(u : ℂ) * (r : ℂ) = (((-(u * r)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_exp]
    push_cast
    ring
  have hpow : ((u ^ alpha : ℝ) : ℂ) =
      Complex.exp ((alpha : ℂ) * Complex.log (u : ℂ)) := by
    rw [← Complex.ofReal_log hu.le]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    rw [Real.rpow_def_of_pos hu]
    congr 1
    ring
  calc
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (-(u : ℂ) * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ∫ r in Set.Ioi (0 : ℝ),
        (((Real.exp (-(u * r)) - 1) *
          r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with r
            exact hfun r
    _ = (((∫ r in Set.Ioi (0 : ℝ),
          (Real.exp (-(u * r)) - 1) *
            r ^ (-alpha - 1) ∂volume) : ℝ) : ℂ) := by
          exact _root_.integral_ofReal
    _ = ((Real.Gamma (-alpha) * u ^ alpha : ℝ) : ℂ) := by
          rw [hreal]
    _ = ((Real.Gamma (-alpha) : ℝ) : ℂ) *
          Complex.exp ((alpha : ℂ) * Complex.log (u : ℂ)) := by
          rw [Complex.ofReal_mul, hpow]
