-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaNegativeFrequencyPhase
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:57:27.190295+00:00
-- url     : https://prove2.me/submissions/776ed865-861d-4f67-9770-d537bb1feaa7

import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open Complex Real Set Kyprianou.Ch01
set_option autoImplicit false

theorem solution (alpha xi : ℝ) (hxi : xi < 0) :
    Complex.exp ((alpha : ℂ) *
      Complex.log (-(Complex.I * (xi : ℂ)))) =
      ((|xi| ^ alpha : ℝ) : ℂ) *
        Complex.exp (Complex.I * (((Real.pi * alpha / 2 : ℝ) : ℂ))) := by
  have hpos : 0 < -xi := neg_pos.mpr hxi
  have hneg : -(Complex.I * (xi : ℂ)) =
      Complex.I * ((-xi : ℝ) : ℂ) := by
    push_cast
    ring
  have hlog : Complex.log (-(Complex.I * (xi : ℂ))) =
        ((Real.log (-xi) : ℝ) : ℂ) +
          (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    calc
      Complex.log (-(Complex.I * (xi : ℂ))) =
          Complex.log (Complex.I * ((-xi : ℝ) : ℂ)) :=
            congrArg Complex.log hneg
      _ = ((Real.log (-xi) : ℝ) : ℂ) + Complex.log Complex.I :=
        Complex.log_mul_ofReal (-xi) hpos Complex.I (by simp)
      _ = _ := by rw [Complex.log_I]; push_cast; ring
  have hrpow : Complex.exp ((alpha : ℂ) *
      ((Real.log (-xi) : ℝ) : ℂ)) =
      (((-xi) ^ alpha : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    simp [Real.rpow_def_of_pos hpos, mul_comm]
  rw [hlog, mul_add, Complex.exp_add, hrpow]
  rw [abs_of_neg hxi]
  congr 1
  push_cast
  ring
