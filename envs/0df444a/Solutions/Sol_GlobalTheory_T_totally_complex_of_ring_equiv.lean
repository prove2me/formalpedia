-- Prove2me | solution 1 for GlobalTheory.T.totally_complex_of_ring_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:27.265348+00:00
-- url     : https://prove2.me/submissions/d833f17f-b8d1-4b84-8846-9c93250b16bf

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TotallyComplexOfRingEquiv
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TotallyComplexOfRingEquivStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_isTotallyComplex_of_ringEquiv


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
theorem _root_.solution : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), IsTotallyComplex F → IsTotallyComplex F' := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv | exact GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv <;> assumption)
end _root_.GlobalTheory.T
