-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_factorial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:38:48.885075+00:00
-- url     : https://prove2.me/submissions/d7638988-49d9-44ac-bef7-3b9e859de0f1

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_unit
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by
  apply OAI.PiExponent.DeterminantContradiction.simplexVolume_unit <;> assumption
