-- Prove2me | solution 1 for MagicSquares.interior_functional_eq_nat_two
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-21T22:25:10.952457+00:00
-- url     : https://prove2.me/submissions/27b6a6d2-c551-41d7-aa20-41b55a8bd6a5

import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_semi_magic_count_two

open MagicSquares

theorem poly_eq_zero_of_nat_eval_eq_zero {p : Polynomial Rat} (h : forall r : Nat, p.eval (r : Rat) = 0) :
    p = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot p ?_
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (f := fun r : Nat => (r : Rat)) Nat.cast_injective)
  rintro x ⟨r, rfl⟩
  exact h r

theorem solution (p : Polynomial Rat) (hp : forall t : Nat, p.eval (t : Rat) = (semiMagicCount 2 t : Rat)) (u : Nat) :
    p.eval (-(((2 + u : Nat)) : Rat)) = (-1 : Rat) ^ ((2 - 1) ^ 2) * p.eval ((u : Rat)) := by
  have hQeval : forall t : Nat, (Polynomial.X + Polynomial.C 1 : Polynomial Rat).eval (t : Rat) = ((t + 1 : Nat) : Rat) := fun t => by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    push_cast
    ring
  have hH : forall t : Nat, (semiMagicCount 2 t : Rat) = ((t + 1 : Nat) : Rat) := fun t => by
    rw [semi_magic_count_two t]
  have hpQ : forall r : Nat, p.eval (r : Rat) = (Polynomial.X + Polynomial.C 1 : Polynomial Rat).eval (r : Rat) := fun r => by
    rw [hp r]
    rw [hH r]
    rw [hQeval r]
  have hP : p = Polynomial.X + Polynomial.C 1 := by
    have hzero : p - (Polynomial.X + Polynomial.C 1) = 0 := by
      apply poly_eq_zero_of_nat_eval_eq_zero
      intro r
      rw [Polynomial.eval_sub]
      rw [hpQ r]
      simp
    exact sub_eq_zero.mp hzero
  rw [hP]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  push_cast
  ring
