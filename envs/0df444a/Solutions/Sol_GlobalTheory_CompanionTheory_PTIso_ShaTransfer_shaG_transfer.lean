-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.ShaTransfer.shaG_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:49:14.709032+00:00
-- url     : https://prove2.me/submissions/4b7dcaa6-339c-4c07-97ae-95638efaf4ac

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TateShafarevichTransport
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_ShaTransfer_dualData_transfer
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_ShaTransfer_nonempty_sha1_equiv
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_ShaTransfer_nonempty_sha2_equiv
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_ShaTransfer_twDual_compat_of_iso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.ShaTransfer
namespace GlobalTheory.CompanionTheory.PTIso.ShaTransfer
theorem _root_.solution {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
    {I I' : Type} [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type}
    [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
    (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))
    (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i))
    (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ)
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i))
    (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hχ : ∀ g, χ' (eG g) = χ g) (hρ : ∀ g m, ρ' (eG g) m = ρ g m)
    (h : ShaG φ' hφ' χ' ρ') : ShaG φ hφ χ ρ := by
  have hT := twDual_compat_of_iso χ χ' ρ ρ' eG hχ hρ
  obtain ⟨a1⟩ := nonempty_sha1_equiv φ hφ φ' hφ' ρ ρ' eG eI eD hD hρ
  obtain ⟨a2⟩ := nonempty_sha2_equiv φ hφ φ' hφ' ρ ρ' eG eI eD hD hρ
  obtain ⟨b1⟩ := nonempty_sha1_equiv φ hφ φ' hφ' (twDual χ ρ) (twDual χ' ρ') eG eI eD hD hT
  obtain ⟨b2⟩ := nonempty_sha2_equiv φ hφ φ' hφ' (twDual χ ρ) (twDual χ' ρ') eG eI eD hD hT
  exact ⟨dualData_transfer b1 a2 h.1, dualData_transfer a1 b2 h.2⟩
end GlobalTheory.CompanionTheory.PTIso.ShaTransfer
