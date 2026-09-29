-- Prove2me | solution 2 for MagicSquares.total_sum_eq_n_line_sum
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:16:46.888361+00:00
-- url     : https://prove2.me/submissions/31b04b9c-055b-428c-99dd-40a7d93e3adc

import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- The total is the sum of the `n` row sums, each equal to `s`. -/
theorem solution {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsSemiMagic M s) :
    totalSum M = n • s := by
  calc
    totalSum M = ∑ i : Fin n, rowSum M i := by simp [totalSum, rowSum]
    _ = ∑ i : Fin n, s := by simp [hM.1]
    _ = n • s := by
          rw [Finset.sum_const, Finset.card_univ]
          simp
