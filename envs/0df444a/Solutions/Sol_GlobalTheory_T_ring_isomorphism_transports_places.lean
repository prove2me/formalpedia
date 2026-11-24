-- Prove2me | solution 1 for GlobalTheory.T.ring_isomorphism_transports_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:22:20.473282+00:00
-- url     : https://prove2.me/submissions/17020171-3f99-4a9f-911c-422c86c45808

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingIsomorphismTransportsPlaces
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingIsomorphismTransportsPlacesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_Places_exists_places_of_ringEquiv


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
theorem _root_.solution : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), ∃ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) ∧ ∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.Places.exists_places_of_ringEquiv | exact GlobalTheory.CompanionTheory.PTIso.Places.exists_places_of_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.Places.exists_places_of_ringEquiv <;> assumption)
end _root_.GlobalTheory.T
