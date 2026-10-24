-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.intervalIntegral_one_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:04.862935+00:00
-- url     : https://prove2.me/submissions/04fc69a6-159a-4606-8ea9-6762144b7b05

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib

open MeasureTheory Filter Topology in

theorem solution (n : Nat) :
    ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) =
      ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by
  congr 1
  rw [intervalIntegral.integral_comp_sub_left (fun t => t ^ n)]
  simp [integral_pow]
