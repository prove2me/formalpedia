-- Prove2me | solution 1 for MagicSquares.magic_three_param_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:37:41.438117+00:00
-- url     : https://prove2.me/submissions/ab5c0357-3662-457e-be28-6eaa574aed18

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- Every line of `mkMagic3` sums to `3 * e`; the admissibility inequalities are
exactly the non-truncation side conditions for the four subtractions. -/
theorem solution (e a c : ℕ) (h : IsParam3 e a c) :
    IsMagic (mkMagic3 e a c) (3 * e) := by
  rcases h with ⟨hl, hu, ha, hc⟩
  have ha2 : a ≤ 2 * e := by omega
  have hc2 : c ≤ 2 * e := by omega
  constructor
  · constructor
    · intro i
      fin_cases i <;> simp [mkMagic3, rowSum, Fin.sum_univ_three]
      all_goals omega
    · intro j
      fin_cases j <;> simp [mkMagic3, colSum, Fin.sum_univ_three]
      all_goals omega
  · constructor
    · simp [mkMagic3, diagSum, Fin.sum_univ_three]
      omega
    · simp [mkMagic3, antiDiagSum, Fin.sum_univ_three]
      omega
