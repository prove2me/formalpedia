-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.exists_gsIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:09:44.151165+00:00
-- url     : https://prove2.me/submissions/839cbb24-643e-4372-a7ea-3886720cb8e7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InertiaQuotientTransport
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_map_mem_closedNormal
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_subgroupIso_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.PTIso.subgroupIso_coe



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso
namespace GlobalTheory.CompanionTheory.PTIso
theorem _root_.solution : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') → ∀ (T : Set (HeightOneSpectrum (𝓞 F))) (T' : Set (HeightOneSpectrum (𝓞 F'))), (∀ v, v ∈ T ↔ eV v ∈ T') → ∃ Ψ : GS Ω T ≃ₜ* GS Ω' T', ∀ σ : G F Ω, Ψ (toGS Ω T σ) = toGS Ω' T' (Φ σ) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E _ Φ _ eV hP hI T T' hT
  have hfwd : ∀ σ, σ ∈ NS Ω T → Φ σ ∈ NS Ω' T' := by
    intro σ hσ
    refine map_mem_closedNormal Φ _ _ ?_ hσ
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ ⊢
    obtain ⟨v, hv, A, hA, hτ⟩ := hτ
    let A' : ValuationSubring Ω' := A.comap (E.symm : Ω' →+* Ω)
    have hAA : ∀ x, E x ∈ A' ↔ x ∈ A := by
      intro x
      show E.symm (E x) ∈ A ↔ x ∈ A
      simp
    exact ⟨eV v, fun h => hv ((hT v).2 h), A', (hP A A' hAA v).1 hA, (hI A A' hAA τ).1 hτ⟩
  have hbwd : ∀ σ', σ' ∈ NS Ω' T' → Φ.symm σ' ∈ NS Ω T := by
    intro σ' hσ'
    refine map_mem_closedNormal Φ.symm _ _ ?_ hσ'
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ ⊢
    obtain ⟨v', hv', A', hA', hτ⟩ := hτ
    let A : ValuationSubring Ω := A'.comap (E : Ω →+* Ω')
    have hAA : ∀ x, E x ∈ A' ↔ x ∈ A := fun x => Iff.rfl
    refine ⟨eV.symm v', fun h => hv' ?_, A, ?_, ?_⟩
    · simpa using (hT _).1 h
    · refine (hP A A' hAA _).2 ?_
      simpa using hA'
    · refine (hI A A' hAA _).2 ?_
      simpa using hτ
  have hiff : ∀ σ, σ ∈ NS Ω T ↔ Φ σ ∈ NS Ω' T' := fun σ =>
    ⟨hfwd σ, fun h => by simpa using hbwd _ h⟩
  exact ⟨quotientIso Φ (NS Ω T) (NS Ω' T') hiff, fun σ => rfl⟩
end GlobalTheory.CompanionTheory.PTIso
