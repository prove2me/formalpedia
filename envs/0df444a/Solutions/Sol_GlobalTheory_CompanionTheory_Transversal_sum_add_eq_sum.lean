-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:38.761807+00:00
-- url     : https://prove2.me/submissions/77156dc0-1f73-4e69-8f51-4ae080427667

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSumsProportionalCard

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
theorem _root_.solution {X : Type} [AddCommGroup X] {M : Type} [AddCommGroup M]
    {A H : AddSubgroup X} {T : Finset X}
    (hTA : ∀ t ∈ T, t ∈ A) (hT : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (F : X → M) (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) {a : X} (ha : a ∈ A) :
    ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by
  have hex : ∀ t ∈ T, ∃ s, s ∈ T ∧ (t + a) - s ∈ H := fun t ht =>
    (hT (t + a) (A.add_mem (hTA t ht) ha)).exists
  choose! φ hφT hφH using hex
  refine Finset.sum_bij (fun t _ => φ t) (fun t ht => hφT t ht) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ he
    have he' : φ t₁ = φ t₂ := he
    have hd : t₁ - t₂ ∈ H := by
      have := H.sub_mem (hφH t₁ h₁) (hφH t₂ h₂)
      rw [he'] at this
      have e : (t₁ + a - φ t₂) - (t₂ + a - φ t₂) = t₁ - t₂ := by abel
      rwa [e] at this
    have h0 : t₁ - t₁ ∈ H := by simp [H.zero_mem]
    exact (hT t₁ (hTA t₁ h₁)).unique ⟨h₁, h0⟩ ⟨h₂, hd⟩
  · intro s hs
    obtain ⟨t, ⟨ht, hd⟩, -⟩ := hT (s - a) (A.sub_mem (hTA s hs) ha)
    refine ⟨t, ht, ?_⟩
    have h1 : (t + a) - s ∈ H := by
      have := H.neg_mem hd
      have e : -(s - a - t) = t + a - s := by abel
      rwa [e] at this
    have h0 : (t + a) - (φ t) ∈ H := hφH t ht
    have hA : t + a ∈ A := A.add_mem (hTA t ht) ha
    exact (hT (t + a) hA).unique ⟨hφT t ht, h0⟩ ⟨hs, h1⟩
  · intro t ht
    have := hF (φ t) _ (hφH t ht)
    have e : φ t + (t + a - φ t) = t + a := by abel
    rwa [e] at this
end GlobalTheory.CompanionTheory.Transversal
