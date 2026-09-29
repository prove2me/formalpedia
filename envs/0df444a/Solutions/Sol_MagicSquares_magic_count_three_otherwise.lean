-- Prove2me | solution 1 for MagicSquares.magic_count_three_otherwise
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T13:45:01.656735+00:00
-- url     : https://prove2.me/submissions/168e77a0-0979-4d52-96d3-79b163037b85

import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_center_of_order_three

set_option autoImplicit false

open MagicSquares

/-- Reduction of `MagicSquares.magic_count_three_otherwise` to
`MagicSquares.center_of_order_three`.

If a `3 × 3` magic square of line sum `t` exists, then by
`center_of_order_three` its centre entry `c` satisfies `3 c = t`, so `3 ∣ t`.
Hence for `t` not divisible by `3` the finset `magicSquares 3 t` is empty and
`M_3(t) = 0`. -/
theorem solution (t : ℕ) (ht : ¬ 3 ∣ t) : magicCount 3 t = 0 := by
  classical
  rw [magicCount, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨M, hM⟩
  have hm : IsMagic (fun i j : Fin 3 => (M i j : ℕ)) t := by
    simpa [magicSquares] using hM
  have hc := center_of_order_three (fun i j : Fin 3 => (M i j : ℕ)) t hm
  exact ht ⟨(M 1 1 : ℕ), hc.symm⟩
