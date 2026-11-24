-- Prove2me | solution 1 for GlobalTheory.T.norm_mul_apply_le_of_ultrametric
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:16:39.538371+00:00
-- url     : https://prove2.me/submissions/cb14418f-af62-4a80-b122-2216521330d4

import Mathlib


theorem solution : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (A B : Matrix n n E) (a b : ℝ), 0 ≤ a → 0 ≤ b → (∀ i j, ‖A i j‖ ≤ a) → (∀ i j, ‖B i j‖ ≤ b) → ∀ i j, ‖(A * B) i j‖ ≤ a * b := by
  intro E _ _ n _ _ A B a b ha hb hA hB i j
  rw [Matrix.mul_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb)
  intro k hk; rw [norm_mul]; exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha
