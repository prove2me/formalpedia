-- Prove2me | solution 1 for MagicSquares.interior_functional_eq_nat
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:46:23.745553+00:00
-- url     : https://prove2.me/submissions/764f2e16-1796-4313-a5da-4858f288cc48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_interior_functional_eq_nat_one
import Theorems.Thm_MagicSquares_interior_functional_eq_nat_two
import Theorems.Thm_MagicSquares_interior_functional_eq_nat_three
import Theorems.Thm_MagicSquares_interior_functional_eq_nat_four
import Theorems.Thm_MagicSquares_interior_functional_eq_nat_ge_five

open MagicSquares

theorem _root_.solution (n : Nat) (hn : 1 <= n) (p : Polynomial Rat)
    (hp : forall t : Nat, p.eval (t : Rat) = (semiMagicCount n t : Rat)) (u : Nat) :
    p.eval (-(((n + u : Nat)) : Rat)) = (-1 : Rat) ^ ((n - 1) ^ 2) * p.eval ((u : Rat)) := by
  by_cases h5 : 5 ≤ n
  · exact MagicSquares.interior_functional_eq_nat_ge_five n h5 p hp u
  · push_neg at h5
    interval_cases n
    · exact MagicSquares.interior_functional_eq_nat_one p hp u
    · exact MagicSquares.interior_functional_eq_nat_two p hp u
    · exact MagicSquares.interior_functional_eq_nat_three p hp u
    · exact MagicSquares.interior_functional_eq_nat_four p hp u

#print axioms solution
