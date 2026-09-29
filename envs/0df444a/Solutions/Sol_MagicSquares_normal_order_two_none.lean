-- Prove2me | solution 1 for MagicSquares.normal_order_two_none
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T12:28:53.325062+00:00
-- url     : https://prove2.me/submissions/1d04619a-af22-4a66-8caf-cd6104fadddd

import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

/-- Solution for `MagicSquares.normal_order_two_none`.

Comparing the first row `a + b = s` with the main diagonal `a + d = s` forces
`b = d`, contradicting injectivity of the index-to-entry map on the two distinct
cells `(0,1)` and `(1,1)`. -/
theorem solution : ¬ ∃ (M : Square 2 ℕ) (s : ℕ), IsNormal M ∧ IsMagic M s := by
  rintro ⟨M, s, hN, hM⟩
  have hrow : M 0 0 + M 0 1 = s := by
    simpa [rowSum, Fin.sum_univ_two] using hM.1.1 (0 : Fin 2)
  have hdiag : M 0 0 + M 1 1 = s := by
    simpa [diagSum, Fin.sum_univ_two] using hM.2.1
  have hboth : M 0 0 + M 0 1 = M 0 0 + M 1 1 := by rw [hrow, hdiag]
  have heq : M 0 1 = M 1 1 := Nat.add_left_cancel hboth
  have hp : ((0 : Fin 2), (1 : Fin 2)) = ((1 : Fin 2), (1 : Fin 2)) := hN.2 heq
  exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) (congrArg Prod.fst hp)
