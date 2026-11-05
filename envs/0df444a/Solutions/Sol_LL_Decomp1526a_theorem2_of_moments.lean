-- Prove2me | solution 1 for LL_Decomp1526a.theorem2_of_moments
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:16.240019+00:00
-- url     : https://prove2.me/submissions/66a7bedd-e964-4500-b7a4-9aee7c15aefb

import Mathlib
import Definitions.Def_LL_Decomp1526a_IsGoldbachSum
import Definitions.Def_LL_Decomp1526a_rep
import Definitions.Def_LL_Decomp1526a_evenBlock
import Definitions.Def_LL_Decomp1526a_Theorem2

open Finset Real
open scoped Chebyshev Classical

theorem solution (L U : ℝ) (hL : 0 < L) (hU : 0 < U) (hc : 1 / 5 ≤ L ^ 2 / U)
    (h1 : ∀ X : ℝ, exp 67 ≤ X →
      L * X ^ 2 ≤ ∑ N ∈ LL_Decomp1526a.evenBlock X, LL_Decomp1526a.rep N)
    (h2 : ∀ X : ℝ, exp 67 ≤ X →
      ∑ N ∈ LL_Decomp1526a.evenBlock X, LL_Decomp1526a.rep N ^ 2 ≤ U * X ^ 3) :
    LL_Decomp1526a.Theorem2 := by
  intro X hX
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  set G := (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter
    (fun N => Even N ∧ LL_Decomp1526a.IsGoldbachSum N) with hG
  have hGsub : G ⊆ LL_Decomp1526a.evenBlock X := by
    intro N hN
    simp only [hG, mem_filter] at hN
    simp only [LL_Decomp1526a.evenBlock, mem_filter]
    exact ⟨hN.1, hN.2.1⟩
  have hzero : ∀ N ∈ LL_Decomp1526a.evenBlock X, N ∉ G → LL_Decomp1526a.rep N = 0 := by
    intro N hN hNG
    have hNG' : ¬ LL_Decomp1526a.IsGoldbachSum N := by
      intro hgb
      apply hNG
      simp only [LL_Decomp1526a.evenBlock, mem_filter] at hN
      simp only [hG, mem_filter]
      exact ⟨hN.1, hN.2, hgb⟩
    unfold LL_Decomp1526a.rep
    apply sum_eq_zero
    intro p hp
    simp only [mem_filter, mem_range] at hp
    rw [if_neg]
    intro hq
    exact hNG' ⟨p, N - p, hp.2, hq, by omega⟩
  have hS1 : ∑ N ∈ LL_Decomp1526a.evenBlock X, LL_Decomp1526a.rep N =
      ∑ N ∈ G, LL_Decomp1526a.rep N := (sum_subset hGsub hzero).symm
  have hS2 : ∑ N ∈ G, LL_Decomp1526a.rep N ^ 2 ≤ U * X ^ 3 :=
    le_trans (sum_le_sum_of_subset_of_nonneg hGsub (fun _ _ _ => sq_nonneg _)) (h2 X hX)
  have hCS := sum_mul_sq_le_sq_mul_sq G (fun N => LL_Decomp1526a.rep N) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, nsmul_eq_mul] at hCS
  have h3 : L * X ^ 2 ≤ ∑ N ∈ G, LL_Decomp1526a.rep N := hS1 ▸ h1 X hX
  have h4 : (L * X ^ 2) ^ 2 ≤ U * X ^ 3 * (#G : ℝ) := by
    calc (L * X ^ 2) ^ 2 ≤ (∑ N ∈ G, LL_Decomp1526a.rep N) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h3 2
      _ ≤ _ := hCS
      _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right hS2 (Nat.cast_nonneg _)
  have h5 : U / 5 ≤ L ^ 2 := by
    rw [le_div_iff₀ hU] at hc
    linarith
  have h6 : U * X ^ 3 * (X / 5) ≤ U * X ^ 3 * (#G : ℝ) := by
    calc U * X ^ 3 * (X / 5) = U / 5 * X ^ 4 := by ring
      _ ≤ L ^ 2 * X ^ 4 := by gcongr
      _ = (L * X ^ 2) ^ 2 := by ring
      _ ≤ _ := h4
  exact le_of_mul_le_mul_left h6 (by positivity)
