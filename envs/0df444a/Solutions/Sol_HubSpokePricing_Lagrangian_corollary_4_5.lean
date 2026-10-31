-- Prove2me | solution 1 for HubSpokePricing.Lagrangian.corollary_4_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:04:23.111993+00:00
-- url     : https://prove2.me/submissions/90681aa4-c16a-4b65-9fc5-4097ab3ec157
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_HubSpokePricing_Lagrangian_Model
import Theorems.Thm_HubSpokePricing_Lagrangian_lemma_4_4

open HubSpokePricing.Lagrangian

theorem solution (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδm : δ < N.m)
    (lam : ℝ) (hlam : IsDualOpt N δ lam)
    (sol : Fin N.n → SpokeSol N.m) (hsol : ∀ i, SpokeOptimal N lam i (sol i))
    (μ : OrigState N → ℝ) (hμ : MarkovChain.IsStationary (origKernel N sol) μ) :
    hubEmptyProb N μ ≤ relaxDepletionProb N sol := by
  have h := (lemma_4_4 N hN δ hδ0 hδm lam hlam sol hsol μ hμ).2 0
  have hL : hubEmptyProb N μ =
      ∑ x : OrigState N, if (N.m : ℤ) - ∑ i, ((x.1 i : ℕ) : ℤ) ≤ 0 then μ x else 0 := by
    unfold hubEmptyProb
    apply Finset.sum_congr rfl
    intro x _
    have hx := x.2
    have hc : ∑ i, ((x.1 i : ℕ) : ℤ) = ((∑ i, (x.1 i : ℕ) : ℕ) : ℤ) := by push_cast; rfl
    rw [hc]
    by_cases h1 : ∑ i, (x.1 i : ℕ) = N.m
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
  have hR : relaxDepletionProb N sol =
      ∑ x : RelaxState N, if (N.m : ℤ) - ∑ i, ((x i : ℕ) : ℤ) ≤ 0 then prodLaw N sol x else 0 := by
    unfold relaxDepletionProb
    apply Finset.sum_congr rfl
    intro x _
    have hc : ∑ i, ((x i : ℕ) : ℤ) = ((∑ i, (x i : ℕ) : ℕ) : ℤ) := by push_cast; rfl
    rw [hc]
    by_cases h1 : N.m ≤ ∑ i, (x i : ℕ)
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
  rw [hL, hR]; exact h
