-- Prove2me | solution 1 for GlobalTheory.sum_transversal_left_translate_invariant
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:03:44.208113+00:00
-- url     : https://prove2.me/submissions/d14afe96-160c-4529-bf5b-681323ad2d72

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
theorem _root_.solution :
    ∀ {G X : Type} [Group G] [AddCommMonoid X] (H K : Subgroup G) (R : Finset G) (f : G → X),
      (∀ r ∈ R, r ∈ H) → (∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K) →
      (∀ r ∈ H, ∀ c ∈ K, f (r * c) = f r) → ∀ k ∈ H, ∑ r ∈ R, f (k * r) = ∑ r ∈ R, f r := by
  intro G X _ _ H K R f hR htr hf k hk
  classical
  -- σ r is the representative of k * r
  have hex : ∀ r ∈ R, ∃! s, s ∈ R ∧ s⁻¹ * (k * r) ∈ K := fun r hr => htr _ (H.mul_mem hk (hR r hr))
  choose σ hσ huniq using hex
  have hval : ∀ r (hr : r ∈ R), f (k * r) = f (σ r hr) := by
    intro r hr
    have h := hf (σ r hr) (hR _ (hσ r hr).1) ((σ r hr)⁻¹ * (k * r)) (hσ r hr).2
    rwa [mul_inv_cancel_left] at h
  refine Finset.sum_bij (fun r hr => σ r hr) (fun r hr => (hσ r hr).1) ?_ ?_ (fun r hr => hval r hr)
  · intro a ha b hb hab
    -- both a and b represent the same coset
    have h1 : (σ a ha)⁻¹ * (k * a) ∈ K := (hσ a ha).2
    have h2 : (σ a ha)⁻¹ * (k * b) ∈ K := by rw [hab]; exact (hσ b hb).2
    have h3 : a⁻¹ * b ∈ K := by
      have := K.mul_mem (K.inv_mem h1) h2
      simpa [mul_assoc] using this
    have hu := htr b (hR b hb)
    exact hu.unique ⟨ha, h3⟩ ⟨hb, by rw [inv_mul_cancel]; exact K.one_mem⟩
  · intro s hs
    have hks : k⁻¹ * s ∈ H := H.mul_mem (H.inv_mem hk) (hR s hs)
    obtain ⟨r, ⟨hr, hrk⟩, _⟩ := htr _ hks
    refine ⟨r, hr, ?_⟩
    have : s⁻¹ * (k * r) ∈ K := by
      have := K.inv_mem hrk
      simpa [mul_assoc] using this
    exact (huniq r hr s ⟨hs, this⟩).symm

