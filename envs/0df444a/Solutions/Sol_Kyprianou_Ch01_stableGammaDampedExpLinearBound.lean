-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaDampedExpLinearBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:23:12.719165+00:00
-- url     : https://prove2.me/submissions/4b69354f-eb3f-45bd-b262-a2d61ca755b7

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_complexPureImaginaryExponentialLipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real
set_option autoImplicit false

/-- Exact damped Fourier exponential is uniformly Lipschitz near zero. -/
theorem solution
    (w : ℂ) (hwre : w.re = 0) (epsilon x : ℝ)
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1‖ ≤
      (‖w‖ + 2) * x := by
  let E0 : ℂ := Complex.exp (w * (x : ℂ))
  let E1 : ℂ := Complex.exp (-((epsilon * x : ℝ) : ℂ))
  have hexact : Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1 =
      E0 * (E1 - 1) + (E0 - 1) := by
    dsimp [E0, E1]
    have harg : (w - (epsilon : ℂ)) * (x : ℂ) =
        w * (x : ℂ) + -((epsilon * x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, Complex.exp_add]
    ring
  have hepsx0 : 0 ≤ epsilon * x := mul_nonneg he0 hx.le
  have hepsx1 : epsilon * x ≤ 1 := by
    calc
      epsilon * x ≤ 1 * x := mul_le_mul_of_nonneg_right he1 hx.le
      _ = x := by ring
      _ ≤ 1 := hx1
  have hy : ‖(-((epsilon * x : ℝ) : ℂ))‖ ≤ 1 := by
    simpa [Complex.norm_real, abs_mul, abs_of_nonneg he0, abs_of_nonneg hx.le] using hepsx1
  have hdecay : ‖E1 - 1‖ ≤ 2 * (epsilon * x) := by
    dsimp [E1]
    have h := Complex.norm_exp_sub_one_le hy
    simpa [Complex.norm_real, abs_mul, abs_of_nonneg he0, abs_of_nonneg hx.le] using h
  have hosc : ‖E0 - 1‖ ≤ ‖w‖ * x := by
    exact Kyprianou.Ch01.complexPureImaginaryExponentialLipschitz
      w hwre x hx.le
  have hnosc : ‖E0‖ = 1 := by
    dsimp [E0]
    rw [Complex.norm_exp]
    have hre : (w * (x : ℂ)).re = 0 := by
      simp [Complex.mul_re, hwre]
    rw [hre]
    simp
  calc
    ‖Complex.exp ((w - (epsilon : ℂ)) * (x : ℂ)) - 1‖ =
      ‖E0 * (E1 - 1) + (E0 - 1)‖ := by rw [hexact]
    _ ≤ ‖E0‖ * ‖E1 - 1‖ + ‖E0 - 1‖ := by
      simpa [norm_mul] using norm_add_le (E0 * (E1 - 1)) (E0 - 1)
    _ ≤ 2 * (epsilon * x) + ‖w‖ * x := by
      rw [hnosc, one_mul]
      exact add_le_add hdecay hosc
    _ ≤ (‖w‖ + 2) * x := by
      nlinarith [mul_le_mul_of_nonneg_right he1 hx.le]
