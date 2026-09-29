-- Prove2me | solution 1 for Gilbreath.head_odd_tail_even
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T19:20:23.375494+00:00
-- url     : https://prove2.me/submissions/e12dcb3a-691b-4010-900b-5f235ab8d965

import Definitions.Def_gilbreath_triangle

open Gilbreath

private theorem nth_prime_zero_eq_two : Nat.nth Nat.Prime 0 = 2 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 2) = 2 :=
    Nat.nth_count (p := Nat.Prime) (n := 2) (by norm_num)
  rwa [show Nat.count Nat.Prime 2 = 0 from by decide] at h

private theorem nth_prime_one_eq_three : Nat.nth Nat.Prime 1 = 3 := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime 3) = 3 :=
    Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
  rwa [show Nat.count Nat.Prime 3 = 1 from by decide] at h

/-- Every prime after the first is odd. -/
private theorem nth_prime_succ_mod_two (n : ℕ) : Nat.nth Nat.Prime (n + 1) % 2 = 1 := by
  have hp := Nat.prime_nth_prime (n + 1)
  have hlt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime (n + 1) :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 (by omega)
  rw [nth_prime_zero_eq_two] at hlt
  exact Nat.odd_iff.1 (hp.odd_of_ne_two (by omega))

theorem solution (k : ℕ) :
    Odd (d (k + 1) 0) ∧ ∀ n : ℕ, Even (d (k + 1) (n + 1)) := by
  induction k with
  | zero =>
    constructor
    · rw [Nat.odd_iff, d_succ_apply, d_zero_apply, d_zero_apply, nth_prime_zero_eq_two,
        nth_prime_one_eq_three]
      decide
    · intro n
      have h1 := nth_prime_succ_mod_two n
      have h2 := nth_prime_succ_mod_two (n + 1)
      rw [Nat.even_iff, d_succ_apply, d_zero_apply, d_zero_apply]
      omega
  | succ k ih =>
    obtain ⟨hodd, heven⟩ := ih
    rw [Nat.odd_iff] at hodd
    constructor
    · have h1 := Nat.even_iff.1 (heven 0)
      rw [Nat.odd_iff, d_succ_apply]
      omega
    · intro n
      have h1 := Nat.even_iff.1 (heven n)
      have h2 := Nat.even_iff.1 (heven (n + 1))
      rw [Nat.even_iff, d_succ_apply]
      omega
