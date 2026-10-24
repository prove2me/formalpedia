-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_47e3ceaa
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:34:22.796898+00:00
-- url     : https://prove2.me/submissions/6a7506cc-3bf0-44e5-acce-bccde943fb8c

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_succ_mul_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_zero_for_induction
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_inverse_factorial_succ_ennreal
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / ((Nat.factorial n : Nat) : Real)) *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by
  have hvol : ∀ k : Nat,
      MeasureTheory.volume
          {x : Fin k → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
        ENNReal.ofReal (1 / ((Nat.factorial k : Nat) : Real)) := by
    intro k
    induction k with
    | zero =>
        exact OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_for_induction
    | succ k ih =>
        rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_mul_volume k, ih]
        exact OAI.PiExponent.DeterminantContradiction.inverse_factorial_succ_ennreal k
  rw [← hvol n]
  exact OAI.PiExponent.DeterminantContradiction.simplexVolume_succ_mul_volume n