-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.ShaTransfer.res_h2_iso_h2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:55:16.340527+00:00
-- url     : https://prove2.me/submissions/20b655da-de8e-45d4-b40f-39b537489014

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TateShafarevichTransport

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
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (i : I) (x : H2 σ') :
    resH2 σ (φ i) (hφ i) (equivH2OfIso eG σ' σ hσ x) =
      equivH2OfIso (eD i) (σ'.comp (φ' (eI i))) (σ.comp (φ i)) (local_compat φ φ' σ σ' eG eI eD hD hσ i)
        (resH2 σ' (φ' (eI i)) (hφ' (eI i)) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext d
    show f.1 (eG (φ i d.1), eG (φ i d.2)) = f.1 (φ' (eI i) (eD i d.1), φ' (eI i) (eD i d.2))
    rw [hD, hD]
end GlobalTheory.CompanionTheory.PTIso.ShaTransfer
