-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:06:49.948982+00:00
-- url     : https://prove2.me/submissions/c6febb26-a972-415c-8ba4-64f802cde00d

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_factorial_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_factorial_succ_step
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by
  induction n with
  | zero => exact OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_zero
  | succ n ih =>
      exact OAI.PiExponent.DeterminantContradiction.simplexVolume_factorial_succ_step n ih