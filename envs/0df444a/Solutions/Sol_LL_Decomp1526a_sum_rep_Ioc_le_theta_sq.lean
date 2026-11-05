-- Prove2me | solution 1 for LL_Decomp1526a.sum_rep_Ioc_le_theta_sq
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:14.710903+00:00
-- url     : https://prove2.me/submissions/91b4dcc1-d1ef-463c-b93d-c416c89259a1

import Mathlib
import Definitions.Def_LL_Decomp1526a_rep

open Finset Real
open scoped Chebyshev Classical

theorem solution (a b : ℕ) :
    ∑ N ∈ Ioc a b, LL_Decomp1526a.rep N ≤ θ (b : ℝ) ^ 2 := by
  have h1 : ∀ N : ℕ, LL_Decomp1526a.rep N =
      ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime),
        Real.log p * Real.log ((N - p : ℕ) : ℝ) := by
    intro N
    unfold LL_Decomp1526a.rep
    rw [← sum_filter, filter_filter]
  simp_rw [h1]
  rw [sum_sigma', Chebyshev.theta_eq_sum_primesLE_log, sq, sum_mul_sum, ← sum_product']
  have hinj : Set.InjOn (fun x : (Σ _ : ℕ, ℕ) => (x.2, x.1 - x.2))
      (((Ioc a b).sigma (fun N => (range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime)) :
        Finset (Σ _ : ℕ, ℕ)) : Set (Σ _ : ℕ, ℕ)) := by
    rintro ⟨N, p⟩ hx ⟨M, q⟩ hy hxy
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, mem_range] at hx hy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    subst h1
    have : N = M := by omega
    subst this
    rfl
  rw [← sum_image (f := fun y : ℕ × ℕ => Real.log (y.1 : ℝ) * Real.log (y.2 : ℝ)) hinj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro y hy
    simp only [mem_image, mem_sigma, mem_Ioc, mem_filter, mem_range] at hy
    obtain ⟨⟨N, p⟩, ⟨⟨_, hNb⟩, hpN, hp, hq⟩, rfl⟩ := hy
    dsimp only at hNb hpN hp hq ⊢
    simp only [mem_product, Nat.mem_primesLE]
    exact ⟨⟨by omega, hp⟩, by omega, hq⟩
  · intro y hy _
    simp only [mem_product, Nat.mem_primesLE] at hy
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hy.1.2.one_lt.le))
      (Real.log_nonneg (by exact_mod_cast hy.2.2.one_lt.le))
