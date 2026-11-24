-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:55:23.847285+00:00
-- url     : https://prove2.me/submissions/8fc09481-067e-4eb8-877e-04534de59979

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TotallyComplexOfRingEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso
namespace GlobalTheory.CompanionTheory.PTIso
theorem _root_.solution : ∀ (F F' : Type) [Field F] [NumberField F] [Field F']
    [NumberField F'] (e : F ≃+* F'), IsTotallyComplex F → IsTotallyComplex F' := by
  intro F F' _ _ _ _ e h
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  have hr : (w.comap (e : F →+* F')).IsReal := (InfinitePlace.isReal_comap_iff e).2 hw
  exact InfinitePlace.not_isReal_iff_isComplex.2 (h.isComplex _) hr
end GlobalTheory.CompanionTheory.PTIso
