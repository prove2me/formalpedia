-- Prove2me | solution 1 for MagicSquares.interior_functional_eq_nat_three
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-22T01:02:40.175386+00:00
-- url     : https://prove2.me/submissions/bdc4ea2a-b09c-4f1c-8dee-d8f3d7fab847

import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_semi_magic_count_three

open MagicSquares

theorem poly_eq_zero_of_nat_eval_eq_zero {p : Polynomial Rat} (h : forall r : Nat, p.eval (r : Rat) = 0) :
    p = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot p ?_
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (f := fun r : Nat => (r : Rat)) Nat.cast_injective)
  rintro x ⟨r, rfl⟩
  exact h r

noncomputable def Q3 : Polynomial Rat :=
  Polynomial.C (1 / 8 : Rat) * ((Polynomial.X + Polynomial.C 3) * (Polynomial.X + Polynomial.C 2) * (Polynomial.X + Polynomial.C 1) * Polynomial.X) +
  Polynomial.C (1 / 2 : Rat) * ((Polynomial.X + Polynomial.C 2) * (Polynomial.X + Polynomial.C 1))

theorem solution (p : Polynomial Rat) (hp : forall t : Nat, p.eval (t : Rat) = (semiMagicCount 3 t : Rat)) (u : Nat) :
    p.eval (-(((3 + u : Nat)) : Rat)) = (-1 : Rat) ^ ((3 - 1) ^ 2) * p.eval ((u : Rat)) := by
  have hQeval : forall t : Nat, Q3.eval (t : Rat) = (semiMagicCount 3 t : Rat) := fun t => by
    rw [semi_magic_count_three t]
    cases t with
    | zero =>
      have h03 : (0 + 3).choose 4 = 0 := by decide
      have h02 : (0 + 2).choose 2 = 1 := by decide
      rw [h03, h02]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      unfold Q3
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
      push_cast
      norm_num
    | succ k =>
      have h4le : 4 <= k + 1 + 3 := by omega
      have h2le : 2 <= k + 1 + 2 := by omega
      have h4 := Nat.choose_mul_factorial_mul_factorial h4le
      have h2 := Nat.choose_mul_factorial_mul_factorial h2le
      have hsub4 : k + 1 + 3 - 4 = k := by omega
      have hsub2 : k + 1 + 2 - 2 = k + 1 := by omega
      rw [hsub4] at h4
      rw [hsub2] at h2
      have hfact4 : Nat.factorial (k + 1 + 3) = (k + 4) * (k + 3) * (k + 2) * (k + 1) * Nat.factorial k := by
        have eA : k + 1 + 3 = (k + 3) + 1 := by omega
        have eB : k + 3 = (k + 2) + 1 := by omega
        have eC : k + 2 = (k + 1) + 1 := by omega
        calc Nat.factorial (k + 1 + 3)
          _ = ((k + 3) + 1) * Nat.factorial (k + 3) := by rw [eA, Nat.factorial_succ]
          _ = ((k + 3) + 1) * (((k + 2) + 1) * Nat.factorial (k + 2)) := by rw [eB, Nat.factorial_succ]
          _ = ((k + 3) + 1) * (((k + 2) + 1) * (((k + 1) + 1) * Nat.factorial (k + 1))) := by rw [eC, Nat.factorial_succ]
          _ = ((k + 3) + 1) * (((k + 2) + 1) * (((k + 1) + 1) * ((k + 1) * Nat.factorial k))) := by rw [Nat.factorial_succ k]
          _ = (k + 4) * (k + 3) * (k + 2) * (k + 1) * Nat.factorial k := by ring
      have hfact2 : Nat.factorial (k + 1 + 2) = (k + 3) * (k + 2) * (k + 1) * Nat.factorial k := by
        have eA : k + 1 + 2 = (k + 2) + 1 := by omega
        have eB : k + 2 = (k + 1) + 1 := by omega
        calc Nat.factorial (k + 1 + 2)
          _ = ((k + 2) + 1) * Nat.factorial (k + 2) := by rw [eA, Nat.factorial_succ]
          _ = ((k + 2) + 1) * (((k + 1) + 1) * Nat.factorial (k + 1)) := by rw [eB, Nat.factorial_succ]
          _ = ((k + 2) + 1) * (((k + 1) + 1) * ((k + 1) * Nat.factorial k)) := by rw [Nat.factorial_succ k]
          _ = (k + 3) * (k + 2) * (k + 1) * Nat.factorial k := by ring
      have hfact4c : Nat.factorial 4 = 24 := by decide
      have hfact2c : Nat.factorial 2 = 2 := by decide
      have hfk : Nat.factorial k ≠ 0 := Nat.factorial_ne_zero k
      have hfk1 : Nat.factorial (k + 1) ≠ 0 := Nat.factorial_ne_zero (k + 1)
      have hfact1 : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := Nat.factorial_succ k
      have h4eq : (k + 1 + 3).choose 4 * 24 * Nat.factorial k = (k + 4) * (k + 3) * (k + 2) * (k + 1) * Nat.factorial k := by
        have h4a : (k + 1 + 3).choose 4 * Nat.factorial 4 * Nat.factorial k = Nat.factorial (k + 1 + 3) := h4
        rw [hfact4c] at h4a
        rw [hfact4] at h4a
        exact h4a
      have hC4 : (k + 1 + 3).choose 4 * 24 = (k + 4) * (k + 3) * (k + 2) * (k + 1) :=
        mul_right_cancel₀ hfk h4eq
      have h2eq : (k + 1 + 2).choose 2 * 2 * Nat.factorial (k + 1) = ((k + 3) * (k + 2)) * Nat.factorial (k + 1) := by
        have h2a : (k + 1 + 2).choose 2 * Nat.factorial 2 * Nat.factorial (k + 1) = Nat.factorial (k + 1 + 2) := h2
        rw [hfact2c] at h2a
        rw [hfact2] at h2a
        have h2b : (k + 3) * (k + 2) * (k + 1) * Nat.factorial k = ((k + 3) * (k + 2)) * Nat.factorial (k + 1) := by
          rw [hfact1]
          ring
        rw [h2b] at h2a
        have hassoc : (k + 1 + 2).choose 2 * 2 * Nat.factorial (k + 1) = ((k + 1 + 2).choose 2 * 2) * Nat.factorial (k + 1) := by ring
        have hassoc2 : ((k + 3) * (k + 2)) * Nat.factorial (k + 1) = (k + 3) * (k + 2) * Nat.factorial (k + 1) := by ring
        rw [hassoc] at h2a ⊢
        rw [hassoc2] at h2a ⊢
        exact h2a
      have hC2 : (k + 1 + 2).choose 2 * 2 = (k + 3) * (k + 2) :=
        mul_right_cancel₀ hfk1 h2eq
      have hC4R : ((((k + 1 + 3).choose 4 : Nat)) : Rat) * 24 = (((k : Nat) : Rat) + 4) * ((((k : Nat) : Rat) + 3)) * ((((k : Nat) : Rat) + 2)) * ((((k : Nat) : Rat) + 1)) := by
        have h : ((((k + 1 + 3).choose 4 : Nat)) : Rat) * 24 = ((((k + 4) * (k + 3) * (k + 2) * (k + 1) : Nat)) : Rat) := by
          exact_mod_cast hC4
        have hprod : ((((k + 4) * (k + 3) * (k + 2) * (k + 1) : Nat)) : Rat) = (((k : Nat) : Rat) + 4) * ((((k : Nat) : Rat) + 3)) * ((((k : Nat) : Rat) + 2)) * ((((k : Nat) : Rat) + 1)) := by
          push_cast
          ring
        rw [h]
        exact hprod
      have hC2R : ((((k + 1 + 2).choose 2 : Nat)) : Rat) * 2 = (((k : Nat) : Rat) + 3) * ((((k : Nat) : Rat) + 2)) := by
        have h : ((((k + 1 + 2).choose 2 : Nat)) : Rat) * 2 = ((((k + 3) * (k + 2) : Nat)) : Rat) := by
          exact_mod_cast hC2
        have hprod : ((((k + 3) * (k + 2) : Nat)) : Rat) = (((k : Nat) : Rat) + 3) * ((((k : Nat) : Rat) + 2)) := by
          push_cast
          ring
        rw [h]
        exact hprod
      have hcast : ((((3 * ((k + 1 + 3).choose 4) + ((k + 1 + 2).choose 2) : Nat))) : Rat) = Q3.eval ((((k + 1 : Nat))) : Rat) := by
        unfold Q3
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
        push_cast
        linear_combination (1 / 8 : Rat) * hC4R + (1 / 2 : Rat) * hC2R
      exact hcast.symm
  have hpQ : forall r : Nat, p.eval (r : Rat) = Q3.eval (r : Rat) := fun r => by
    rw [hp r]
    rw [hQeval r]
  have hP : p = Q3 := by
    have hzero : p - Q3 = 0 := by
      apply poly_eq_zero_of_nat_eval_eq_zero
      intro r
      rw [Polynomial.eval_sub]
      rw [hpQ r]
      simp
    exact sub_eq_zero.mp hzero
  rw [hP]
  unfold Q3
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  push_cast
  ring
