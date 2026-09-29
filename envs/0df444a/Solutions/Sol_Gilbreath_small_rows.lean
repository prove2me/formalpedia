-- Prove2me | solution 1 for Gilbreath.small_rows
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T19:20:25.185837+00:00
-- url     : https://prove2.me/submissions/145392c8-88d2-4e22-827e-22633c364817

import Definitions.Def_gilbreath_triangle

open Gilbreath

private theorem nth_prime_eq (i v c : ℕ) (hv : Nat.Prime v) (hc : Nat.count Nat.Prime v = c)
    (hic : i = c) : Nat.nth Nat.Prime i = v := by
  have h : Nat.nth Nat.Prime (Nat.count Nat.Prime v) = v := Nat.nth_count hv
  rwa [hc, ← hic] at h

theorem solution (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) : d k 0 = 1 := by
  have p0 : Nat.nth Nat.Prime 0 = 2 := nth_prime_eq 0 2 0 (by norm_num) (by decide) rfl
  have p1 : Nat.nth Nat.Prime 1 = 3 := nth_prime_eq 1 3 1 (by norm_num) (by decide) rfl
  have p2 : Nat.nth Nat.Prime 2 = 5 := nth_prime_eq 2 5 2 (by norm_num) (by decide) rfl
  have p3 : Nat.nth Nat.Prime 3 = 7 := nth_prime_eq 3 7 3 (by norm_num) (by decide) rfl
  have p4 : Nat.nth Nat.Prime 4 = 11 := nth_prime_eq 4 11 4 (by norm_num) (by decide) rfl
  have h10 : d 1 0 = 1 := by
    rw [d_succ_apply, d_zero_apply, d_zero_apply, p0, p1]
    decide
  have h11 : d 1 1 = 2 := by
    rw [d_succ_apply, d_zero_apply, d_zero_apply, p1, p2]
    decide
  have h12 : d 1 2 = 2 := by
    rw [d_succ_apply, d_zero_apply, d_zero_apply, p2, p3]
    decide
  have h13 : d 1 3 = 4 := by
    rw [d_succ_apply, d_zero_apply, d_zero_apply, p3, p4]
    decide
  have h20 : d 2 0 = 1 := by rw [d_succ_apply, h10, h11]; decide
  have h21 : d 2 1 = 0 := by rw [d_succ_apply, h11, h12]; decide
  have h22 : d 2 2 = 2 := by rw [d_succ_apply, h12, h13]; decide
  have h30 : d 3 0 = 1 := by rw [d_succ_apply, h20, h21]; decide
  have h31 : d 3 1 = 2 := by rw [d_succ_apply, h21, h22]; decide
  have h40 : d 4 0 = 1 := by rw [d_succ_apply, h30, h31]; decide
  interval_cases k <;> assumption
