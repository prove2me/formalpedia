-- Prove2me | solution 1 for MagicSquares.normal_order_three_associative
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T14:06:15.166379+00:00
-- url     : https://prove2.me/submissions/4f409278-b515-4ef3-aa7b-0c8bc68cb0fe

import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_center_of_order_three
import Theorems.Thm_MagicSquares_normal_order_three_constant

set_option autoImplicit false

open MagicSquares

/-- Reduction of `MagicSquares.normal_order_three_associative`.

Every centrally opposite pair of cells lies together with the centre cell on a row,
a column, or one of the two diagonals. Each of those four lines sums to `s = 15` and
the centre is `5`, so each opposite pair sums to `10`. The nine index pairs are
discharged by case analysis on `Fin 3`. -/
theorem solution (M : Square 3 ℕ) (s : ℕ) (hN : IsNormal M) (hM : IsMagic M s) :
    IsAssociative M 10 := by
  have hs : s = 15 := normal_order_three_constant M s hN hM
  have hc : M 1 1 = 5 := by
    have h3 := center_of_order_three M s hM
    omega
  have hR0 : M 0 0 + M 0 1 + M 0 2 = s := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
  have hR1 : M 1 0 + M 1 1 + M 1 2 = s := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (1 : Fin 3)
  have hR2 : M 2 0 + M 2 1 + M 2 2 = s := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (2 : Fin 3)
  have hC0 : M 0 0 + M 1 0 + M 2 0 = s := by
    simpa [colSum, Fin.sum_univ_three] using hM.1.2 (0 : Fin 3)
  have hC1 : M 0 1 + M 1 1 + M 2 1 = s := by
    simpa [colSum, Fin.sum_univ_three] using hM.1.2 (1 : Fin 3)
  have hC2 : M 0 2 + M 1 2 + M 2 2 = s := by
    simpa [colSum, Fin.sum_univ_three] using hM.1.2 (2 : Fin 3)
  have hD : M 0 0 + M 1 1 + M 2 2 = s := by
    simpa [diagSum, Fin.sum_univ_three] using hM.2.1
  have hA : M 0 2 + M 1 1 + M 2 0 = s := by
    simpa [antiDiagSum, Fin.sum_univ_three] using hM.2.2
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Fin.rev] <;> omega
