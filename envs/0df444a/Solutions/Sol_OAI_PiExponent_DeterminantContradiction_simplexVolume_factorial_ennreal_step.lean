-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_ennreal_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:06.793187+00:00
-- url     : https://prove2.me/submissions/5abe8b6c-c022-46f1-bb11-a50fa7e5e90b

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib
open scoped BigOperators

open MeasureTheory Filter Topology in

theorem solution (n : Nat) :
    ENNReal.ofReal (1 / (Nat.factorial n : Real)) *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) =
      ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ]; push_cast; field_simp
