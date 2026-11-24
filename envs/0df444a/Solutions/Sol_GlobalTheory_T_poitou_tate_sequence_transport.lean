-- Prove2me | solution 1 for GlobalTheory.T.poitou_tate_sequence_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:21:18.613474+00:00
-- url     : https://prove2.me/submissions/92f0ebdb-53bb-4761-a606-ca823e8f6f84

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateSequenceTransport
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateSequenceTransportStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_nineG_of_iso


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type} [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)] [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (ρ' : Representation R Γ' M) (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i)), (∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) → (∀ g, χ' (eG g) = χ g) → (∀ g m, ρ' (eG g) m = ρ g m) → ∀ (j : ∀ i, H2 ((charRep χ).comp (φ i)) →ₗ[R] R) (j' : ∀ i, H2 ((charRep χ').comp (φ' i)) →ₗ[R] R) (hρ : ContAction ρ) (hρ' : ContAction ρ'), (∀ (i : I) (z : Z2 ((charRep χ).comp (φ i))) (z' : Z2 ((charRep χ').comp (φ' (eI i)))), (∀ g h, z'.1 (eD i g, eD i h) = z.1 (g, h)) → j' (eI i) (Submodule.Quotient.mk z') = j i (Submodule.Quotient.mk z)) → NineG φ' hφ' χ' j' ρ' hρ' → NineG φ hφ χ j ρ hρ := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.NineTransfer.nineG_of_iso | exact GlobalTheory.CompanionTheory.PTIso.NineTransfer.nineG_of_iso | (intros; apply GlobalTheory.CompanionTheory.PTIso.NineTransfer.nineG_of_iso <;> assumption)
end _root_.GlobalTheory.T
