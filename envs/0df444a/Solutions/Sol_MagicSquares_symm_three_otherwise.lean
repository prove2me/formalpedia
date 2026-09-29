-- Prove2me | solution 1 for MagicSquares.symm_three_otherwise
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-18T14:15:46.489652+00:00
-- url     : https://prove2.me/submissions/91d14644-115f-4c11-8bed-6a3dee836636

import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_center_of_order_three

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- Solution for `MagicSquares.symm_three_otherwise`.

A symmetric magic square of order three and line sum `t` is in particular magic,
so by `center_of_order_three` its centre entry `c` satisfies `3 c = t`, hence
`3 ∣ t`. Consequently for `t` not divisible by `3` the finset
`symmetricMagicSquares 3 t` is empty and `S_3(t) = 0`.

The only difference from the panmagic case is that the filtering predicate is a
conjunction, so the magic hypothesis has to be projected out first. -/
theorem solution (t : ℕ) (ht : ¬ 3 ∣ t) : symmetricMagicCount 3 t = 0 := by
  classical
  rw [symmetricMagicCount, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨M, hM⟩
  have hpair : IsMagic (fun i j : Fin 3 => (M i j : ℕ)) t ∧
      IsSymmetric (fun i j : Fin 3 => (M i j : ℕ)) := by
    simpa [symmetricMagicSquares] using hM
  have hc := center_of_order_three (fun i j : Fin 3 => (M i j : ℕ)) t hpair.1
  exact ht ⟨(M 1 1 : ℕ), hc.symm⟩
