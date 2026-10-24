-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:33:26.223258+00:00
-- url     : https://prove2.me/submissions/c955b7b6-9739-4bb8-a9b3-b72dcd408cc5

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i) (B : Real) (hB : 0 < B) :
    {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) ≤ B} =
      {x : Fin n → Real | (∀ i, 0 ≤ (w i / B) * x i) ∧
        (∑ i, (w i / B) * x i) ≤ 1} := by
  ext x
  have hsum : (∑ i, (w i / B) * x i) = (∑ i, w i * x i) / B := by
    calc
      (∑ i, (w i / B) * x i) = ∑ i, (w i * x i) / B := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, w i * x i) / B := by rw [Finset.sum_div]
  constructor
  · rintro ⟨hx, hbound⟩
    constructor
    · intro i
      exact (mul_nonneg_iff_of_pos_left (div_pos (hw i) hB)).2 (hx i)
    · rw [hsum]
      exact (div_le_one hB).2 hbound
  · rintro ⟨hx, hbound⟩
    constructor
    · intro i
      exact (mul_nonneg_iff_of_pos_left (div_pos (hw i) hB)).1 (hx i)
    · rw [hsum] at hbound
      exact (div_le_one hB).1 hbound