-- Prove2me | solution 1 for GlobalTheory.NormCurve.isIntegrallyClosed_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:37:14.0801+00:00
-- url     : https://prove2.me/submissions/2bcd6d04-1298-4ac2-afe7-d8658adf3446

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsPrimeLeNotMemRingKrullDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteIntegralClosureOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsProperCurveThroughPoint
import Theorems.Thm_GlobalTheory_NormCurve_exists_eq_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.NormCurve
namespace GlobalTheory.NormCurve
theorem _root_.solution {B R : Type} [CommRing B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) : IsIntegrallyClosed (integralClosure B R) := by
  haveI : IsFractionRing (integralClosure B R) R := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, e⟩ := exists_eq_div h z
    exact ⟨algebraMap B _ x, algebraMap B _ y, e⟩
  exact (isIntegrallyClosed_iff R).mpr fun {x} hx => ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩
end GlobalTheory.NormCurve
