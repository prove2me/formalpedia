-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.ShaTransfer.nonempty_sha1_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:28:00.170242+00:00
-- url     : https://prove2.me/submissions/34147e21-540e-4f7e-892f-c7cbe4e3f172

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TateShafarevichTransport
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_ShaTransfer_nonempty_equiv_of_mem_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_ShaTransfer_mem_Sha1_iff_equiv_mem

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
    (hσ : ∀ g m, σ' (eG g) m = σ g m) :
    Nonempty (Sha1 σ' φ' hφ' ≃ₗ[R] Sha1 σ φ hφ) :=
  nonempty_equiv_of_mem_iff (equivH1OfIso eG σ' σ hσ) _ _
    (mem_Sha1_iff_equiv_mem φ hφ φ' hφ' σ σ' eG eI eD hD hσ)
end GlobalTheory.CompanionTheory.PTIso.ShaTransfer
