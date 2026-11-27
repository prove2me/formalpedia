-- Prove2me | solution 2 for GlobalTheory.sum_transversal_left_translate_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:41:44.556466+00:00
-- url     : https://prove2.me/submissions/ffaeeb35-e97e-46b0-b2e1-dfa329ab272b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumTransversalLeftTranslateInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {G X : Type} [Group G] [AddCommMonoid X] (H K : Subgroup G) (R : Finset G) (f : G → X),
      (∀ r ∈ R, r ∈ H) → (∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K) →
      (∀ r ∈ H, ∀ c ∈ K, f (r * c) = f r) → ∀ k ∈ H, ∑ r ∈ R, f (k * r) = ∑ r ∈ R, f r := by
  intro G X _ _ H K R f hR hU hf k hk
  have hkH : ∀ a ∈ R, k * a ∈ H := fun a ha => H.mul_mem hk (hR a ha)
  refine Finset.sum_bij (fun a ha => Classical.choose (hU (k * a) (hkH a ha)).exists)
    (fun a ha => (Classical.choose_spec (hU (k * a) (hkH a ha)).exists).1) ?_ ?_ ?_
  · intro a₁ ha₁ a₂ ha₂ heq
    have h1 := (Classical.choose_spec (hU (k * a₁) (hkH a₁ ha₁)).exists).2
    have h2 := (Classical.choose_spec (hU (k * a₂) (hkH a₂ ha₂)).exists).2
    rw [heq] at h1
    set r' := Classical.choose (hU (k * a₂) (hkH a₂ ha₂)).exists
    have hm : a₁⁻¹ * a₂ ∈ K := by
      have := K.mul_mem (K.inv_mem h1) h2
      simpa [mul_assoc] using this
    have hu := (hU a₂ (hR a₂ ha₂)).unique (y₁ := a₁) (y₂ := a₂) ⟨ha₁, hm⟩ ⟨ha₂, by simpa using K.one_mem⟩
    exact hu
  · intro b hb
    have hb' : k⁻¹ * b ∈ H := H.mul_mem (H.inv_mem hk) (hR b hb)
    obtain ⟨a, ⟨ha, haK⟩, -⟩ := hU (k⁻¹ * b) hb'
    refine ⟨a, ha, ?_⟩
    have hs := Classical.choose_spec (hU (k * a) (hkH a ha)).exists
    have hbK : b⁻¹ * (k * a) ∈ K := by
      have := K.inv_mem haK
      simpa [mul_assoc] using this
    exact (hU (k * a) (hkH a ha)).unique hs ⟨hb, hbK⟩
  · intro a ha
    have hs := Classical.choose_spec (hU (k * a) (hkH a ha)).exists
    set r' := Classical.choose (hU (k * a) (hkH a ha)).exists
    have := hf r' (hR r' hs.1) (r'⁻¹ * (k * a)) hs.2
    rw [mul_inv_cancel_left] at this
    exact this
end GlobalTheory
