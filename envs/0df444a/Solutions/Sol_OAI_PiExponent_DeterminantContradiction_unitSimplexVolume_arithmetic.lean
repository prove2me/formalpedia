-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:25:47.639452+00:00
-- url     : https://prove2.me/submissions/a78ddfd1-5960-4237-a8e5-de1d104f4527

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem solution (n : Nat)
    (h : MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real))) :
    ENNReal.ofReal (1 / (n + 1 : Real)) *
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by
  rw [h, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp