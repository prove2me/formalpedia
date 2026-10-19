-- Prove2me | solution 1 for GreenTao.iterated_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:36:37.752736+00:00
-- url     : https://prove2.me/submissions/41225ef9-5fc3-418d-87bc-ef44cd87e9b1

import Mathlib

open scoped BigOperators

theorem solution (d : ℕ) (hd : 1 ≤ d) (J P : ℕ → ℝ)
    (hstep : ∀ l < d, |J l| ^ 2 ≤ P l * J (l + 1)) :
    |J 0| ^ (2 ^ d) ≤ J d * ∏ l ∈ Finset.range d, P l ^ (2 ^ (d - 1 - l)) := by
  revert hstep
  induction d, hd using Nat.le_induction with
  | base =>
    intro hstep
    simpa [mul_comm] using hstep 0 (by omega)
  | succ n hn ih =>
    intro hstep
    have hi := ih (fun l hl => hstep l (by omega))
    let B : ℝ := ∏ l ∈ Finset.range n, P l ^ (2 ^ (n - 1 - l))
    have hprod : (∏ l ∈ Finset.range (n + 1), P l ^ (2 ^ ((n + 1) - 1 - l))) = P n * B ^ 2 := by
      rw [Finset.prod_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, pow_one]
      rw [mul_comm]
      congr 1
      dsimp [B]
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro l hl
      have he : n - l = (n - 1 - l) + 1 := by have hh := Finset.mem_range.mp hl; omega
      rw [he, pow_succ, pow_mul]
    have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ |J 0| ^ (2 ^ n)) hi 2
    have hs := mul_le_mul_of_nonneg_right (hstep n (by omega)) (sq_nonneg B)
    rw [sq_abs] at hs
    calc
      |J 0| ^ (2 ^ (n + 1)) = (|J 0| ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
      _ ≤ (J n * B) ^ 2 := hsquare
      _ = (J n) ^ 2 * B ^ 2 := mul_pow _ _ _
      _ ≤ (P n * J (n + 1)) * B ^ 2 := hs
      _ = _ := by rw [hprod]; ring
