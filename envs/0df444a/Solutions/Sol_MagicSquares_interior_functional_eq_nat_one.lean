-- Prove2me | solution 1 for MagicSquares.interior_functional_eq_nat_one
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-21T22:23:00.891233+00:00
-- url     : https://prove2.me/submissions/c4e9e809-e8b4-4c46-9a72-c35c868c128e

import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_semi_magic_count_one

open MagicSquares

theorem poly_eq_zero_of_nat_eval_eq_zero {p : Polynomial Rat} (h : forall r : Nat, p.eval (r : Rat) = 0) :
    p = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot p ?_
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (f := fun r : Nat => (r : Rat)) Nat.cast_injective)
  rintro x ⟨r, rfl⟩
  exact h r

theorem solution (p : Polynomial Rat) (hp : forall t : Nat, p.eval (t : Rat) = (semiMagicCount 1 t : Rat)) (u : Nat) :
    p.eval (-(((1 + u : Nat)) : Rat)) = (-1 : Rat) ^ ((1 - 1) ^ 2) * p.eval ((u : Rat)) := by
  have hH : forall t : Nat, (semiMagicCount 1 t : Rat) = 1 := fun t => by
    rw [semi_magic_count_one t]
    simp
  have hp1 : forall r : Nat, p.eval (r : Rat) = 1 := fun r => by
    rw [hp r]
    exact hH r
  have hP : p = Polynomial.C 1 := by
    have hzero : p - Polynomial.C 1 = 0 := by
      apply poly_eq_zero_of_nat_eval_eq_zero
      intro r
      rw [Polynomial.eval_sub, Polynomial.eval_C]
      rw [hp1 r]
      simp
    exact sub_eq_zero.mp hzero
  rw [hP]
  simp
