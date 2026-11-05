-- Prove2me | solution 1 for LL_Decomp1526a.sum_rep_odd_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:13.862441+00:00
-- url     : https://prove2.me/submissions/a713a593-b951-4415-857b-6dda50836b2c

import Mathlib
import Definitions.Def_LL_Decomp1526a_rep

open Finset Real
open scoped Chebyshev Classical

namespace GbBAux

theorem rep_of_odd {N : ℕ} (hN : ¬ Even N) :
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

end GbBAux

theorem solution (a b : ℕ) :
    ∑ N ∈ (Ioc a b).filter (fun N => ¬ Even N), LL_Decomp1526a.rep N ≤
      2 * Real.log 2 * θ (b : ℝ) := by
  set S := (Ioc a b).filter (fun N => ¬ Even N) with hS
  have h1 : ∑ N ∈ S, LL_Decomp1526a.rep N =
      2 * Real.log 2 * ∑ N ∈ S.filter (fun N => (N - 2).Prime), Real.log ((N - 2 : ℕ) : ℝ) := by
    rw [mul_sum]
    conv_rhs => rw [sum_filter]
    apply sum_congr rfl
    intro N hN
    rw [hS, mem_filter] at hN
    rw [GbBAux.rep_of_odd hN.2]
  rw [h1]
  have hl : 0 ≤ 2 * Real.log 2 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hl
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  have hinj : Set.InjOn (fun N : ℕ => N - 2) (S.filter (fun N => (N - 2).Prime) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
    have := hx.2.two_le
    have := hy.2.two_le
    simp only at hxy
    omega
  rw [← sum_image (f := fun q : ℕ => Real.log (q : ℝ)) hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro q hq
    simp only [mem_image, mem_filter, hS, mem_Ioc] at hq
    obtain ⟨N, ⟨⟨⟨_, hNb⟩, _⟩, hNq⟩, rfl⟩ := hq
    rw [Nat.mem_primesLE]
    exact ⟨by omega, hNq⟩
  · intro q hq _
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
