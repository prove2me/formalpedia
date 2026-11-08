-- Prove2me | solution 1 for MenuCostPricing.claim_B_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:08:58.878829+00:00
-- url     : https://prove2.me/submissions/6d31eb1b-8e38-4cf0-8d18-e1945fff86cb

import Mathlib
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy

open MenuCostPricing in
theorem solution {n T : ℕ} (u : Fin n → ℕ) (N : Fin T → ℕ) (Y Bc : Fin T → Fin n → ℕ → Bool) :
    (∀ t i, coupledProxyDemand N Y Bc t i ≤ coupledDemand N Y t i) ∧
    (∀ t i, invLevel (u i) (fun τ => coupledDemand N Y τ i) t ≤
      invLevel (u i) (fun τ => coupledProxyDemand N Y Bc τ i) t) := by
  have h1 : ∀ t i, coupledProxyDemand N Y Bc t i ≤ coupledDemand N Y t i := by
    intro t i
    unfold coupledProxyDemand coupledDemand countUpTo
    apply Finset.card_le_card
    intro ν hν
    simp only [Finset.mem_filter, Bool.and_eq_true] at hν ⊢
    exact ⟨hν.1, hν.2.2⟩
  refine ⟨h1, fun t i => ?_⟩
  unfold invLevel
  apply max_le_max le_rfl
  apply sub_le_sub_left
  apply Finset.sum_le_sum
  intro τ _
  exact_mod_cast h1 τ i
