-- Prove2me | solution 1 for GlobalTheory.T.exists_local_unit_of_dvr_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:19:50.884838+00:00
-- url     : https://prove2.me/submissions/74671151-3379-42fb-b0d1-2fb87d02317f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalUnitOfDvrUnit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalUnitOfDvrUnitStatement
import Theorems.Thm_GlobalTheory_unitMultiple_descends_of_height_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] (𝔭 : PrimeSpectrum A),
    𝔭.asIdeal.height = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (iT : Localization.AtPrime 𝔭.asIdeal →+* V), Function.Injective iT → IsLocalHom iT → ∀ a b : A,
    (∃ w : Vˣ, iT (algebraMap A _ a) = iT (algebraMap A _ b) * w) →
    ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ, (u : Localization.AtPrime 𝔭.asIdeal) * algebraMap A _ b = algebraMap A _ a := by
  first | exact @GlobalTheory.unitMultiple_descends_of_height_eq_one | exact GlobalTheory.unitMultiple_descends_of_height_eq_one | (intros; apply GlobalTheory.unitMultiple_descends_of_height_eq_one <;> assumption)
end _root_.GlobalTheory.T
