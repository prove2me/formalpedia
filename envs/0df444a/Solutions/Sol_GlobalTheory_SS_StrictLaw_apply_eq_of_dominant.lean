-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.apply_eq_of_dominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:20:38.801775+00:00
-- url     : https://prove2.me/submissions/70dce48f-17e0-4f29-8465-59edab68a66a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational
import Theorems.Thm_GlobalTheory_EqualityOnPoints_eq_on_points


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictLaw
namespace GlobalTheory.SS.StrictLaw
theorem _root_.solution {W X Y Z : Scheme.{0}} {a b : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (hs : a ≫ s = b ≫ s) (i : W ⟶ X) [IsDominant i] (hi : i ≫ a = i ≫ b) (x : X) : a x = b x := by
  first
  | (rename_i h_7 h_10; revert W X Y Z a b s h_7 hs i h_10 hi x; exact @_root_.GlobalTheory.EqualityOnPoints.eq_on_points)
  | exact @_root_.GlobalTheory.EqualityOnPoints.eq_on_points
  | exact _root_.GlobalTheory.EqualityOnPoints.eq_on_points
  | (apply _root_.GlobalTheory.EqualityOnPoints.eq_on_points <;> assumption)
  | (intros; apply _root_.GlobalTheory.EqualityOnPoints.eq_on_points <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EqualityOnPoints.eq_on_points <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EqualityOnPoints.eq_on_points ..)
end GlobalTheory.SS.StrictLaw
