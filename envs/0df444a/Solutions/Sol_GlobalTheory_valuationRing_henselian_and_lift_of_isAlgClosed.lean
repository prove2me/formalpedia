-- Prove2me | solution 1 for GlobalTheory.valuationRing_henselian_and_lift_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:03:31.564469+00:00
-- url     : https://prove2.me/submissions/745b8e97-96bf-4c80-90ac-06b18432fc54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingHenselianAndSmoothPointsLift
import Theorems.Thm_GlobalTheory_henselianLocalRing_of_valuationRing_of_isAlgClosed
import Theorems.Thm_GlobalTheory_isAlgClosed_residueField_of_valuationRing_of_isAlgClosed
import Theorems.Thm_GlobalTheory_reducePoint_residue_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K], HenselianLocalRing O ∧ IsAlgClosed (IsLocalRing.ResidueField O) ∧ ∀ (X : Scheme.{0}) (f : X ⟶ Sp O), Smooth f → ∀ x : Sp (IsLocalRing.ResidueField O) ⟶ X, x ≫ f = spMap (IsLocalRing.residue O) → ∃ y : Sp O ⟶ X, y ≫ f = 𝟙 _ ∧ spMap (IsLocalRing.residue O) ≫ y = x := by
  intro O K _ _ _ _ _ _ _
  have := henselianLocalRing_of_valuationRing_of_isAlgClosed O K
  refine ⟨inferInstance, isAlgClosed_residueField_of_valuationRing_of_isAlgClosed O K, ?_⟩
  intro X f hf x hx
  have := hf
  obtain ⟨⟨y, hy⟩, hy'⟩ := reducePoint_residue_surjective f O (𝟙 _) ⟨x, by simpa using hx⟩
  refine ⟨y, hy, ?_⟩
  exact congrArg Subtype.val hy'
end GlobalTheory
