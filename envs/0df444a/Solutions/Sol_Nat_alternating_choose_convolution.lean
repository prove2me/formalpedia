-- Prove2me | solution 1 for Nat.alternating_choose_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:27:17.955476+00:00
-- url     : https://prove2.me/submissions/caf9034a-23df-4c59-997c-4c40e6942b66

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination

open Finset

set_option autoImplicit false

theorem solution {R : Type*} [CommRing R] (n m : ℕ) :
    (∑ k ∈ range (n + 1), (n.choose k : R) * (-1 : R)^k * (k.choose m : R)) =
      if m = n then (-1 : R)^n else 0 := by
  classical
  by_cases hmn : m ≤ n
  · have hz : ∀ k ∈ range m,
        (n.choose k : R) * (-1 : R)^k * (k.choose m : R) = 0 := by
      intro k hk
      simp [Nat.choose_eq_zero_of_lt (mem_range.mp hk)]
    have hs := sum_range_add_sum_Ico
      (fun k => (n.choose k : R) * (-1 : R)^k * (k.choose m : R)) (by omega : m ≤ n+1)
    rw [sum_eq_zero hz, zero_add] at hs
    rw [← hs, sum_Ico_eq_sum_range]
    have hal : (∑ k ∈ range (n-m+1), (-1 : R)^k * ((n-m).choose k : R)) =
        if n-m = 0 then 1 else 0 := by
      have h := congrArg (fun z : ℤ => (z : R)) (Int.alternating_sum_range_choose (n := n-m))
      simpa only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg,
        Int.cast_one, Int.cast_natCast, Int.cast_ite, Int.cast_zero] using h
    have he : n+1-m = n-m+1 := by omega
    rw [he]
    calc
      _ = (n.choose m : R) * (-1 : R)^m *
          (∑ k ∈ range (n-m+1), (-1 : R)^k * ((n-m).choose k : R)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k hk
        have h := congrArg (fun z : ℕ => (z : R))
          (Nat.choose_mul (n := n) (k := m+k) (s := m) (by omega))
        simp only [Nat.cast_mul, Nat.add_sub_cancel_left] at h
        rw [pow_add]
        linear_combination (-1 : R)^m * (-1 : R)^k * h
      _ = _ := by
        rw [hal]
        by_cases h : m = n
        · subst m; simp
        · have hn : n-m ≠ 0 := by omega
          simp [h, hn]
  · rw [if_neg (by omega : m ≠ n)]
    apply sum_eq_zero
    intro k hk
    simp [Nat.choose_eq_zero_of_lt (by have := mem_range.mp hk; omega : k < m)]
