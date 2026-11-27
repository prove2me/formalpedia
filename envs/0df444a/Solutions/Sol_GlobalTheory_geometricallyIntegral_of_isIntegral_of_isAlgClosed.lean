-- Prove2me | solution 1 for GlobalTheory.geometricallyIntegral_of_isIntegral_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:26.09758+00:00
-- url     : https://prove2.me/submissions/477cd3e7-3f74-481f-9843-b9926af5fa05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Theorems.Thm_GlobalTheory_geometricallyIrreducible_of_isAlgClosed
import Theorems.Thm_GlobalTheory_ReducedSubgroup_geometricallyReduced_of_perfectField


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
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Over (Sp k)) [IsIntegral X.left],
      LocallyOfFiniteType X.hom → GeometricallyIntegral X.hom := by
  intro k _ _ X _ h
  have h₁ : GeometricallyReduced X.hom :=
    ReducedSubgroup.geometricallyReduced_of_perfectField (k := k) X.hom
  have h₂ : GeometricallyIrreducible X.hom :=
    geometricallyIrreducible_of_isAlgClosed (k := k) X.hom
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible X.hom
end GlobalTheory
