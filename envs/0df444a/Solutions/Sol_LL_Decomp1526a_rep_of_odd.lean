-- Prove2me | solution 1 for LL_Decomp1526a.rep_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:13.07019+00:00
-- url     : https://prove2.me/submissions/1790262b-fe7c-41eb-b095-64e6be437e44

import Mathlib
import Definitions.Def_LL_Decomp1526a_rep

open Finset Real
open scoped Chebyshev Classical

theorem solution {N : ℕ} (hN : ¬ Even N) :
    LL_Decomp1526a.rep N =
      if (N - 2).Prime then 2 * Real.log 2 * Real.log ((N - 2 : ℕ) : ℝ) else 0 := by
  unfold LL_Decomp1526a.rep
  have key : ∀ p ∈ (range (N + 1)).filter Nat.Prime, (N - p).Prime → p = 2 ∨ p = N - 2 := by
    intro p hp hq
    simp only [mem_filter, mem_range] at hp
    obtain ⟨hpN, hp⟩ := hp
    rcases hp.eq_two_or_odd' with h | h
    · exact Or.inl h
    · rcases hq.eq_two_or_odd' with h' | h'
      · right; omega
      · exfalso; apply hN
        have : N = p + (N - p) := by omega
        rw [this]; exact h.add_odd h'
  by_cases hq : (N - 2).Prime
  · have hN2 : 2 < N - 2 + 1 := by have := hq.two_le; omega
    have hN4 : N ≠ 4 := by rintro rfl; exact hN (by decide)
    have hne : (2 : ℕ) ≠ N - 2 := by
      intro h; apply hN; have : N = 4 := by omega
      rw [this]; decide
    rw [if_pos hq, ← sum_subset (s₁ := {2, N - 2}) ?_ ?_]
    · rw [sum_pair hne]
      have h2 : (N - (N - 2)) = 2 := by
        have := hq.two_le; omega
      rw [h2, if_pos Nat.prime_two, if_pos hq]
      push_cast
      ring
    · intro p hp
      simp only [mem_insert, mem_singleton] at hp
      simp only [mem_filter, mem_range]
      rcases hp with rfl | rfl
      · exact ⟨by have := hq.two_le; omega, Nat.prime_two⟩
      · exact ⟨by omega, hq⟩
    · intro p hp hp'
      by_cases hq' : (N - p).Prime
      · exfalso; apply hp'
        rcases key p hp hq' with rfl | rfl <;> simp
      · rw [if_neg hq']
  · rw [if_neg hq]
    apply sum_eq_zero
    intro p hp
    by_cases hq' : (N - p).Prime
    · exfalso
      rcases key p hp hq' with rfl | rfl
      · exact hq hq'
      · simp only [mem_filter, mem_range] at hp
        exact hq hp.2
    · rw [if_neg hq']
