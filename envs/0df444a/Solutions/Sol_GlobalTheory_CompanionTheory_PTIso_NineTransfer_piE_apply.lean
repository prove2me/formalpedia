-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.NineTransfer.piE_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:26.068469+00:00
-- url     : https://prove2.me/submissions/7fd6a172-0639-41c5-a259-0cd3fafd1ec9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateSequenceTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.NineTransfer
variable {R : Type*} [CommRing R]
namespace GlobalTheory.CompanionTheory.PTIso.NineTransfer
theorem _root_.solution {I I' : Type*} {A : I' → Type*} {B : I → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module R (B i)] (eI : I ≃ I') (e : ∀ i, A (eI i) ≃ₗ[R] B i) (x : ∀ i', A i') (i : I) :
    piE eI e x i = e i (x (eI i)) := rfl
end GlobalTheory.CompanionTheory.PTIso.NineTransfer
