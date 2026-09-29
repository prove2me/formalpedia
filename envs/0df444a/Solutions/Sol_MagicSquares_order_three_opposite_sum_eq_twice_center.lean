-- Prove2me | solution 1 for MagicSquares.order_three_opposite_sum_eq_twice_center
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:29:30.506575+00:00
-- url     : https://prove2.me/submissions/f6441b75-f0ba-465e-b2cc-2f6dd03101bd

import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- Expand the nine line identities; each opposite pair sits on one of them. -/
theorem solution
    (M : Square 3 ℕ) (s : ℕ) (hM : IsMagic M s) (i j : Fin 3) :
    M i j + M (Fin.rev i) (Fin.rev j) = 2 * M 1 1 := by
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
  fin_cases i <;> fin_cases j <;> simp
  all_goals omega
