-- Prove2me | solution 1 for Gilbreath.row_one_eq_prime_gap
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T19:20:22.56241+00:00
-- url     : https://prove2.me/submissions/07590e7a-d1c3-4bb3-b716-0877ac7bfb87

import Definitions.Def_gilbreath_triangle

open Gilbreath

theorem solution (n : ℕ) :
    d 1 n = Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n := by
  have h : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 (by omega)
  simp only [d_succ_apply, d_zero_apply]
  omega
