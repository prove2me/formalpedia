-- Prove2me | solution 1 for MagicSquares.magic_three_param_necessary
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:37:43.102572+00:00
-- url     : https://prove2.me/submissions/b61f161a-0757-40c3-8a75-27c81d5828ed

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- The eight line identities pin every cell to the parametrized form; the
centre is `e`, the two diagonals give the bottom corners, and the remaining
cells follow from the rows and columns. -/
theorem solution (e : ℕ) (M : Square 3 ℕ)
    (hM : IsMagic M (3 * e)) :
    M = mkMagic3 e (M 0 0) (M 0 2) := by
  have hR0 : M 0 0 + M 0 1 + M 0 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
  have hR1 : M 1 0 + M 1 1 + M 1 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (1 : Fin 3)
  have hR2 : M 2 0 + M 2 1 + M 2 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (2 : Fin 3)
  have hC0 : M 0 0 + M 1 0 + M 2 0 = 3 * e := by
    simpa [colSum, Fin.sum_univ_three] using hM.1.2 (0 : Fin 3)
  have hC1 : M 0 1 + M 1 1 + M 2 1 = 3 * e := by
    simpa [colSum, Fin.sum_univ_three] using hM.1.2 (1 : Fin 3)
  have hC2 : M 0 2 + M 1 2 + M 2 2 = 3 * e := by
    simpa [colSum, Fin.sum_univ_three] using hM.1.2 (2 : Fin 3)
  have hD : M 0 0 + M 1 1 + M 2 2 = 3 * e := by
    simpa [diagSum, Fin.sum_univ_three] using hM.2.1
  have hA : M 0 2 + M 1 1 + M 2 0 = 3 * e := by
    simpa [antiDiagSum, Fin.sum_univ_three] using hM.2.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkMagic3]
  all_goals omega
