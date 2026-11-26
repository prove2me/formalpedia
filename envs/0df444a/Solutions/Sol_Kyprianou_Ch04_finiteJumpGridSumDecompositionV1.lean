-- Prove2me | solution 1 for Kyprianou.Ch04.finiteJumpGridSumDecompositionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:37:15.033911+00:00
-- url     : https://prove2.me/submissions/d6f54ac0-38cd-4da2-bad7-d3b9d2d61e3e

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
open Finset
set_option autoImplicit false

/-- Separate the drift and individual atom contributions in a finite-jump grid sum. -/
theorem solution {ι : Type} (S : Finset ι) (n : ℕ)
    (u v H : ℕ → ℝ) (time mark : ι → ℝ) (c : ℝ)
    (Y : ℝ → ℝ)
    (hY : ∀ t, Y t = c*t + ∑ i ∈ S, if time i ≤ t then mark i else 0)
    (huv : ∀ k ∈ range n, u k ≤ v k) :
    (∑ k ∈ range n, H k * (Y (v k) - Y (u k))) =
      c * (∑ k ∈ range n, H k * (v k - u k)) +
        ∑ i ∈ S, mark i * (∑ k ∈ range n,
          if u k < time i ∧ time i ≤ v k then H k else 0) := by
  classical
  have hterm (k : ℕ) (hk : k ∈ range n) :
      H k * (Y (v k) - Y (u k)) =
        c * (H k * (v k - u k)) + ∑ i ∈ S,
          (if u k < time i ∧ time i ≤ v k then mark i * H k else 0) := by
    rw [hY,hY]
    have heq (i : ι) :
        H k * ((if time i ≤ v k then mark i else 0) -
          (if time i ≤ u k then mark i else 0)) =
          (if u k < time i ∧ time i ≤ v k then mark i * H k else 0) := by
      by_cases h1 : time i ≤ u k
      · simp [h1,h1.trans (huv k hk),not_lt.mpr h1]
      · by_cases h2 : time i ≤ v k <;> simp [h1,h2,lt_of_not_ge h1,mul_comm]
    simp_rw [← heq]
    rw [← mul_sum, sum_sub_distrib]
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, sum_comm]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  by_cases h : u k < time i ∧ time i ≤ v k <;> simp [h]
