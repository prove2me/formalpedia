-- Prove2me | solution 1 for MagicSquares.interior_functional_eq_nat_four
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-21T22:28:49.798816+00:00
-- url     : https://prove2.me/submissions/717005de-1b0e-4d2e-8ac9-1ab7288bdd9d

import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_semi_magic_count_four

open MagicSquares

theorem poly_eq_zero_of_nat_eval_eq_zero {p : Polynomial Rat} (h : forall r : Nat, p.eval (r : Rat) = 0) :
    p = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot p ?_
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (f := fun r : Nat => (r : Rat)) Nat.cast_injective)
  rintro x ⟨r, rfl⟩
  exact h r

noncomputable def Q4 : Polynomial Rat :=
  Polynomial.C (11 / 11340 : Rat) * Polynomial.X ^ 9 +
  Polynomial.C (198 / 11340 : Rat) * Polynomial.X ^ 8 +
  Polynomial.C (1596 / 11340 : Rat) * Polynomial.X ^ 7 +
  Polynomial.C (7560 / 11340 : Rat) * Polynomial.X ^ 6 +
  Polynomial.C (23289 / 11340 : Rat) * Polynomial.X ^ 5 +
  Polynomial.C (48762 / 11340 : Rat) * Polynomial.X ^ 4 +
  Polynomial.C (70234 / 11340 : Rat) * Polynomial.X ^ 3 +
  Polynomial.C (68220 / 11340 : Rat) * Polynomial.X ^ 2 +
  Polynomial.C (40950 / 11340 : Rat) * Polynomial.X +
  Polynomial.C 1

theorem solution (p : Polynomial Rat) (hp : forall t : Nat, p.eval (t : Rat) = (semiMagicCount 4 t : Rat)) (u : Nat) :
    p.eval (-(((4 + u : Nat)) : Rat)) = (-1 : Rat) ^ ((4 - 1) ^ 2) * p.eval ((u : Rat)) := by
  have h11340 : (11340 : Rat) ≠ 0 := by norm_num
  have hQeval : forall t : Nat, Q4.eval (t : Rat) = (semiMagicCount 4 t : Rat) := fun t => by
    have h4 := semi_magic_count_four t
    have hcast : ((11340 * semiMagicCount 4 t : Nat) : Rat) = ((11 * t ^ 9 + 198 * t ^ 8 + 1596 * t ^ 7 + 7560 * t ^ 6 + 23289 * t ^ 5 + 48762 * t ^ 4 + 70234 * t ^ 3 + 68220 * t ^ 2 + 40950 * t + 11340 : Nat) : Rat) := by
      exact_mod_cast h4
    push_cast at hcast
    unfold Q4
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    field_simp
    linarith [hcast]
  have hpQ : forall r : Nat, p.eval (r : Rat) = Q4.eval (r : Rat) := fun r => by
    rw [hp r]
    rw [hQeval r]
  have hP : p = Q4 := by
    have hzero : p - Q4 = 0 := by
      apply poly_eq_zero_of_nat_eval_eq_zero
      intro r
      rw [Polynomial.eval_sub]
      rw [hpQ r]
      simp
    exact sub_eq_zero.mp hzero
  rw [hP]
  unfold Q4
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  push_cast
  ring
