-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.subgroupIso_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:25.626257+00:00
-- url     : https://prove2.me/submissions/153a7c2c-35e5-463b-b72b-4ba91fb1518f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso
namespace GlobalTheory.CompanionTheory.PTIso
theorem _root_.solution {A B : Type} [Group A] [TopologicalSpace A] [Group B]
    [TopologicalSpace B] (Φ : A ≃ₜ* B) (H : Subgroup A) (K : Subgroup B)
    (h : ∀ a, a ∈ H ↔ Φ a ∈ K) (a : H) : ((subgroupIso Φ H K h a : K) : B) = Φ a := rfl
end GlobalTheory.CompanionTheory.PTIso
