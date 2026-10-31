-- Prove2me | solution 1 for IncrKnapsack.PTAS.filtering
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T02:57:24.148624+00:00
-- url     : https://prove2.me/submissions/f17c0047-8e00-4a4b-b978-17f439f3d95f

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model
import Theorems.Thm_IncrKnapsack_PTAS_representation_1

open Classical
open Finset BigOperators
open IncrKnapsack.PTAS

theorem solution (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Shat : Sol I) (hfeas : Feasible I Shat)
    (hgood : ∀ i t, Shat i = some t → IsGood I K ξ t) :
    Feasible I (filt I K (pr I K) Shat) ∧
      (∀ i t, filt I K (pr I K) Shat i = some t → IsGood I K ξ t) ∧
      (1 - eps K) * Psi I (pr I K) Shat ≤ Psi I (pr I K) (filt I K (pr I K) Shat) := by
  have hsub : ∀ i t, filt I K (pr I K) Shat i = some t → Shat i = some t := by
    intro i t h
    unfold filt at h
    split_ifs at h with hc
    exact h
  refine ⟨?_, fun i t h => hgood i t (hsub i t h), ?_⟩
  · intro t
    refine le_trans ?_ (hfeas t)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Sol.set, mem_filter, mem_univ, true_and] at hi ⊢
      obtain ⟨s, hs, hst⟩ := hi
      exact ⟨s, hsub i s hs, hst⟩
    · intro i _ _; exact (hI.w_pos i).le
  · -- profit
    have hpr : ∀ i, 0 ≤ pr I K i := by
      intro i; unfold pr eps; positivity
    have hlam : ∀ t, 0 ≤ lamPlus I t := by
      intro t; unfold lamPlus; exact Finset.sum_nonneg (fun τ _ => hI.lam_nonneg τ)
    have hitem : ∀ i, 0 ≤ psiItem I (pr I K) Shat i := by
      intro i; unfold psiItem
      split
      · exact mul_nonneg (hpr i) (hlam _)
      · exact le_refl _
    set Ψ := Psi I (pr I K) Shat with hΨ
    have hΨnn : 0 ≤ Ψ := by
      rw [hΨ, representation_1]; exact Finset.sum_nonneg (fun i _ => hitem i)
    have hn : (0 : ℝ) < I.n := by exact_mod_cast hI.n_pos
    have hfi : ∀ i, psiItem I (pr I K) (filt I K (pr I K) Shat) i =
        psiItem I (pr I K) Shat i -
          (if psiItem I (pr I K) Shat i ≤ eps K / (I.n : ℝ) * Ψ
            then psiItem I (pr I K) Shat i else 0) := by
      intro i
      by_cases hc : psiItem I (pr I K) Shat i ≤ eps K / (I.n : ℝ) * Ψ
      · rw [if_pos hc, sub_self]
        have : filt I K (pr I K) Shat i = none := by
          unfold filt; rw [if_pos hc]
        unfold psiItem; rw [this]
      · rw [if_neg hc, sub_zero]
        have : filt I K (pr I K) Shat i = Shat i := by
          unfold filt; rw [if_neg hc]
        unfold psiItem; rw [this]
    have hloss : ∑ i, (if psiItem I (pr I K) Shat i ≤ eps K / (I.n : ℝ) * Ψ
            then psiItem I (pr I K) Shat i else 0) ≤ eps K * Ψ := by
      calc ∑ i, (if psiItem I (pr I K) Shat i ≤ eps K / (I.n : ℝ) * Ψ
            then psiItem I (pr I K) Shat i else 0)
          ≤ ∑ _i : Fin I.n, eps K / (I.n : ℝ) * Ψ := by
            apply Finset.sum_le_sum; intro i _
            split_ifs with hc
            · exact hc
            · have : 0 ≤ eps K := by unfold eps; positivity
              positivity
        _ = eps K * Ψ := by
            rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    have : Psi I (pr I K) (filt I K (pr I K) Shat) = Ψ -
        ∑ i, (if psiItem I (pr I K) Shat i ≤ eps K / (I.n : ℝ) * Ψ
            then psiItem I (pr I K) Shat i else 0) := by
      rw [representation_1, contrib, Finset.sum_congr rfl (fun i _ => hfi i),
        Finset.sum_sub_distrib, hΨ, representation_1, contrib]
    rw [this]; linarith
