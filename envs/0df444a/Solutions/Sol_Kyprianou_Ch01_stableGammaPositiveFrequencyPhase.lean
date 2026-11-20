-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaPositiveFrequencyPhase
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:30:45.211979+00:00
-- url     : https://prove2.me/submissions/49c56ad4-5193-410e-bae8-0e6f5255c6c5

import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open Complex Real Set Kyprianou.Ch01
set_option autoImplicit false

theorem solution (alpha xi : ℝ) (hxi : 0 < xi) :
    Complex.exp ((alpha : ℂ) *
      Complex.log (-(Complex.I * (xi : ℂ)))) =
      ((xi ^ alpha : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (((Real.pi * alpha / 2 : ℝ) : ℂ)))) := by
  have hlog :
      Complex.log (-(Complex.I * (xi : ℂ))) =
        ((Real.log xi : ℝ) : ℂ) -
          (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    calc
      Complex.log (-(Complex.I * (xi : ℂ))) =
        Complex.log ((-Complex.I) * (xi : ℂ)) := by ring
      _ = ((Real.log xi : ℝ) : ℂ) + Complex.log (-Complex.I) :=
        Complex.log_mul_ofReal xi hxi (-Complex.I) (by simp)
      _ = _ := by rw [Complex.log_neg_I]; push_cast; ring
  have hrpow :
      Complex.exp ((alpha : ℂ) * ((Real.log xi : ℝ) : ℂ)) =
      ((xi ^ alpha : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    simp [Real.rpow_def_of_pos hxi, mul_comm]
  rw [hlog, mul_sub, Complex.exp_sub]
  rw [hrpow, div_eq_mul_inv, ← Complex.exp_neg]
  congr 1
  push_cast
  ring
