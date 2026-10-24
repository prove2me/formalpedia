-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_for_induction
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:37:34.318728+00:00
-- url     : https://prove2.me/submissions/6e26f2aa-7cc7-4aee-b091-e32c0f081699

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / ((Nat.factorial 0 : Nat) : Real)) := by
  rw [MeasureTheory.Measure.volume_pi_eq_dirac]
  simp