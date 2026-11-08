-- Prove2me | solution 1 for MenuCostPricing.eq_3_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:35:45.570547+00:00
-- url     : https://prove2.me/submissions/cee050d3-0523-40ce-82c7-d98deb3ed580

import Mathlib
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy

open MenuCostPricing in
theorem solution {n L T : ℕ} (I : Instance n L T) (hI : I.Standing) :
    (∀ Γ : Finset (Fin T), (∀ t ∈ Γ, 1 ≤ t.val) → ∀ x : Strategy n L T,
      I.Cvar x ≤ I.B - Γ.card * I.f → (∀ t : Fin T, 1 ≤ t.val → t ∉ Γ → Delta x t = 0) →
      I.Feasible x) ∧
    (∀ x : Strategy n L T, I.Feasible x →
      I.Cvar x ≤ I.B - (changeSet x).card * I.f ∧
      ∀ t : Fin T, 1 ≤ t.val → t ∉ changeSet x → Delta x t = 0) := by
  have hcs : ∀ x : Strategy n L T,
      (laterPeriods T).filter (fun t => 0 < Delta x t) = changeSet x := by
    intro x
    ext t
    simp [laterPeriods, changeSet]
  refine ⟨?_, ?_⟩
  · intro Γ hΓ x hC hD
    unfold Instance.Feasible Instance.Cfixed
    have hsub : (laterPeriods T).filter (fun t => 0 < Delta x t) ⊆ Γ := by
      intro t ht
      rw [Finset.mem_filter] at ht
      by_contra hn
      have h1 : 1 ≤ t.val := (Finset.mem_filter.mp ht.1).2
      have := hD t h1 hn
      omega
    have hcard := Finset.card_le_card hsub
    have hcR : (((laterPeriods T).filter (fun t => 0 < Delta x t)).card : ℝ) ≤ Γ.card := by
      exact_mod_cast hcard
    have := mul_le_mul_of_nonneg_left hcR hI.f_nonneg
    linarith
  · intro x hx
    unfold Instance.Feasible Instance.Cfixed at hx
    rw [hcs] at hx
    refine ⟨by linarith, fun t ht hn => ?_⟩
    by_contra hne
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, Nat.pos_of_ne_zero hne⟩)
