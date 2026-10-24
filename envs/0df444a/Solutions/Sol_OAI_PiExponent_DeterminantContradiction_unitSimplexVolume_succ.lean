-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_succ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:12.995171+00:00
-- url     : https://prove2.me/submissions/2c2d0668-ff6b-4eed-9946-7f1706349e67

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_factorial_aux
open scoped BigOperators

open MeasureTheory Filter Topology in

theorem solution (n : Nat) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
    ENNReal.ofReal
      (1 / ((Nat.factorial n : Real) * ((n + 1 : Nat) : Real))) := by
  rw [OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux (n+1)]
  congr 2
  rw [Nat.factorial_succ]; push_cast; ring
