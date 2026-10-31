-- Prove2me | solution 1 for IncrKnapsack.PTAS.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T02:56:35.179403+00:00
-- url     : https://prove2.me/submissions/77ccdacb-6e7e-4279-b263-8e72928c4db4

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model
import Theorems.Thm_IncrKnapsack_PTAS_representation_1

open Classical
open Finset BigOperators
open IncrKnapsack.PTAS

theorem solution (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K)
    (p : Fin I.n → ℝ) (S : Sol I) :
    (1 / (K : ℝ)) * ∑ ξ ∈ range K, Psi I p (restrictGood I K ξ S) = (1 - eps K) * Psi I p S := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have key : ∀ i, ∑ ξ ∈ range K, psiItem I p (restrictGood I K ξ S) i =
      ((K : ℝ) - 1) * psiItem I p S i := by
    intro i
    unfold psiItem restrictGood
    rcases h : S i with _ | t
    · simp
    · simp only [Option.filter_some]
      trans ∑ ξ ∈ range K, (if (ivl I K t + 1) % K = ξ then (0:ℝ) else p i * lamPlus I t)
      · apply Finset.sum_congr rfl
        intro ξ _
        by_cases hg : (ivl I K t + 1) % K = ξ
        · simp [IsGood, hg]
        · simp [IsGood, hg]
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
      have hc : ((range K).filter (fun ξ => ¬ (ivl I K t + 1) % K = ξ)).card = K - 1 := by
        have hmem : (ivl I K t + 1) % K ∈ range K := by
          simp; exact Nat.mod_lt _ (by omega)
        have := Finset.card_filter_add_card_filter_not
          (s := range K) (fun ξ => (ivl I K t + 1) % K = ξ)
        have h1 : ((range K).filter (fun ξ => (ivl I K t + 1) % K = ξ)).card = 1 := by
          rw [Finset.card_eq_one]; refine ⟨(ivl I K t + 1) % K, ?_⟩
          ext ξ; simp only [mem_filter, mem_singleton]
          constructor
          · rintro ⟨_, h⟩; exact h.symm
          · rintro rfl; exact ⟨hmem, rfl⟩
        rw [card_range] at this; omega
      rw [hc]; push_cast [show 1 ≤ K by omega]; ring
  have hsum : ∑ ξ ∈ range K, Psi I p (restrictGood I K ξ S) = ((K : ℝ) - 1) * Psi I p S := by
    simp only [representation_1, contrib]
    rw [Finset.sum_comm]
    simp only [key, ← Finset.mul_sum]
  rw [hsum, eps]; field_simp
