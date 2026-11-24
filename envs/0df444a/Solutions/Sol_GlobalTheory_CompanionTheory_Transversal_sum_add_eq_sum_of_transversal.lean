-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:39.390063+00:00
-- url     : https://prove2.me/submissions/449a8c20-3311-41ac-b1b2-cc557861770e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSumTranslateInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Transversal
namespace GlobalTheory.CompanionTheory.Transversal
theorem _root_.solution : ∀ {X : Type} [AddCommGroup X] {M : Type} [AddCommMonoid M] {A H : AddSubgroup X}, H ≤ A → ∀ {T : Finset X}, (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) → ∀ (F : X → M), (∀ a, ∀ h ∈ H, F (a + h) = F a) → ∀ {a : X}, a ∈ A → ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by
  intro X _ M _ A H hHA T hTA huniq F hF a ha
  classical
  have hex : ∀ t ∈ T, ∃ t', t' ∈ T ∧ (t + a) - t' ∈ H := fun t ht =>
    (huniq (t + a) (A.add_mem (hTA t ht) ha)).exists
  choose! g hgT hgH using hex
  have uniq : ∀ x ∈ A, ∀ t₁ t₂, t₁ ∈ T → x - t₁ ∈ H → t₂ ∈ T → x - t₂ ∈ H → t₁ = t₂ :=
    fun x hx t₁ t₂ h1 h1' h2 h2' => (huniq x hx).unique ⟨h1, h1'⟩ ⟨h2, h2'⟩
  refine Finset.sum_bij (fun t _ => g t) (fun t ht => hgT t ht) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ heq
    have hd : t₁ - t₂ ∈ H := by
      have h3 := H.sub_mem (hgH t₁ h₁) (hgH t₂ h₂)
      have e : t₁ + a - g t₁ - (t₂ + a - g t₂) = t₁ - t₂ := by rw [heq]; abel
      rwa [e] at h3
    exact uniq t₁ (hTA t₁ h₁) t₁ t₂ h₁ (by rw [sub_self]; exact H.zero_mem) h₂ hd
  · intro t' ht'
    obtain ⟨t, ⟨htT, htH⟩, -⟩ := huniq (t' - a) (A.sub_mem (hTA t' ht') ha)
    refine ⟨t, htT, ?_⟩
    have h1 : t + a - t' ∈ H := by
      have h3 := H.neg_mem htH
      have e : -(t' - a - t) = t + a - t' := by abel
      rwa [e] at h3
    exact uniq (t + a) (A.add_mem (hTA t htT) ha) (g t) t' (hgT t htT) (hgH t htT) ht' h1
  · intro t ht
    have h3 := hF (g t) _ (hgH t ht)
    have e : g t + (t + a - g t) = t + a := by abel
    rw [e] at h3
    exact h3
end GlobalTheory.CompanionTheory.Transversal
