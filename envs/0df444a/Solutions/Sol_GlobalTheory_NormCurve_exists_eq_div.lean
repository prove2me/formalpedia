-- Prove2me | solution 1 for GlobalTheory.NormCurve.exists_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:24:25.12756+00:00
-- url     : https://prove2.me/submissions/e899e0f1-0ea5-4b12-863f-b8d3c0dd018a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsPrimeLeNotMemRingKrullDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteIntegralClosureOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsProperCurveThroughPoint

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
    (h : (algebraMap B R).SurjectiveOnStalks) (z : R) :
    ∃ x y : B, z = algebraMap B R x / algebraMap B R y := by
  obtain ⟨x, r, c, hc, hr, e⟩ := (RingHom.surjective_localRingHom_iff (⊥ : Ideal R)).mp
    (h ⊥ inferInstance) z
  rw [Ideal.mem_bot] at hc hr
  refine ⟨x, r, ?_⟩
  rw [eq_div_iff hr]
  apply mul_left_cancel₀ hc
  rw [← e]
  ring
end GlobalTheory.NormCurve
