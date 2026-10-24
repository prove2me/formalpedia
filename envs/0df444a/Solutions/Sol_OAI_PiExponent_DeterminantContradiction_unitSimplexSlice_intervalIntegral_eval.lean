-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexSlice_intervalIntegral_eval
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:05.852629+00:00
-- url     : https://prove2.me/submissions/214ba21c-c1cc-4ce7-a548-3bdff60744ab

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib

open MeasureTheory

open MeasureTheory Filter Topology in

theorem solution (n : Nat) :
    ∫ t in (0 : Real)..1, (1 - t) ^ n / (n.factorial : Real) =
    1 / ((n + 1).factorial : Real) := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun t => t ^ n)]
  simp [integral_pow, Nat.factorial_succ]
  field_simp
