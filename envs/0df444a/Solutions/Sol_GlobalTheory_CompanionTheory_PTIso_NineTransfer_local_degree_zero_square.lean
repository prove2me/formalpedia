-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.NineTransfer.local_degree_zero_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:27.35162+00:00
-- url     : https://prove2.me/submissions/a45f0707-31f8-4d67-a950-34a25d481416

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateSequenceTransport
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_piE_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_subgroupIso_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.PTIso.subgroupIso_coe


attribute [local simp] GlobalTheory.CompanionTheory.PTIso.NineTransfer.piE_apply

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.NineTransfer
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {Γ Γ' : Type}
  [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type} [Fintype I]
  [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ')
  (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ)
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
  (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i))
  (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) (hχ : ∀ g, χ' (eG g) = χ g)
  (hc : ∀ g m, ρ' (eG g) m = ρ g m)
  (hd : ∀ g f, twDual χ' ρ' (eG g) f = twDual χ ρ g f)
  (hl : ∀ i d m, (ρ'.comp (φ' (eI i))) (eD i d) m = (ρ.comp (φ i)) d m)
namespace GlobalTheory.CompanionTheory.PTIso.NineTransfer
theorem _root_.solution (x : H0 ρ') :
    gloc0 φ ρ (equivH0OfIso eG ρ' ρ hc x) = P0 φ φ' ρ ρ' eI eD hl (gloc0 φ' ρ' x) := by
  funext i
  exact Subtype.ext rfl
end GlobalTheory.CompanionTheory.PTIso.NineTransfer
