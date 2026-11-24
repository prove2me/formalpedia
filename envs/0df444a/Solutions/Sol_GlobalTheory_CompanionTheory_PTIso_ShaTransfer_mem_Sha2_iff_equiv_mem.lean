-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.ShaTransfer.mem_Sha2_iff_equiv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:12:16.333829+00:00
-- url     : https://prove2.me/submissions/66924e8d-0d0c-4ce8-b44e-1f7aedb54ac1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TateShafarevichTransport
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_ShaTransfer_res_h2_iso_h2
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
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.ShaTransfer
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
  {I I' : Type} {D : I → Type} {D' : I' → Type}
  [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))
  (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i))
  {N : Type} [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N]
  (σ : Representation R Γ N) (σ' : Representation R Γ' N)
  (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i))
namespace GlobalTheory.CompanionTheory.PTIso.ShaTransfer
theorem _root_.solution (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (x : H2 σ') :
    x ∈ Sha2 σ' φ' hφ' ↔ equivH2OfIso eG σ' σ hσ x ∈ Sha2 σ φ hφ := by
  simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i
    rw [res_h2_iso_h2 φ hφ φ' hφ' σ σ' eG eI eD hD hσ, h, map_zero]
  · intro h i'
    obtain ⟨i, rfl⟩ := eI.surjective i'
    have hi := h i
    rw [res_h2_iso_h2 φ hφ φ' hφ' σ σ' eG eI eD hD hσ] at hi
    exact (LinearEquiv.map_eq_zero_iff _).1 hi
end GlobalTheory.CompanionTheory.PTIso.ShaTransfer
