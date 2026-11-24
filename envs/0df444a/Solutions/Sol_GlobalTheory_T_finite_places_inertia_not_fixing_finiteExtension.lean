-- Prove2me | solution 1 for GlobalTheory.T.finite_places_inertia_not_fixing_finiteExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:38.322986+00:00
-- url     : https://prove2.me/submissions/cd635df5-1378-4719-8f5b-340d1dfa8489

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinitePlacesInertiaNotFixingFiniteExtension
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinitePlacesInertiaNotFixingFiniteExtensionStatement
import Theorems.Thm_GlobalTheory_InertiaAlmostAll_finite_ramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L], {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ ¬ Ine (F := F) B ≤ L.fixingSubgroup}.Finite := by
  first | exact @GlobalTheory.InertiaAlmostAll.finite_ramified | exact GlobalTheory.InertiaAlmostAll.finite_ramified | (intros; apply GlobalTheory.InertiaAlmostAll.finite_ramified <;> assumption)
end _root_.GlobalTheory.T
