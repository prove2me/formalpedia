-- Prove2me | solution 1 for GlobalTheory.WeightGen.unit_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:26.796262+00:00
-- url     : https://prove2.me/submissions/80ee6e30-70f5-41fd-abe1-7b97e3959e72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeightGen
namespace GlobalTheory.WeightGen
theorem _root_.solution {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A] :
    η[(Over.pullback f).obj A].left ≫ pullback.fst A.hom f = f ≫ η[A].left := by
  have h : η[(Over.pullback f).obj A] =
      Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map η[A] := rfl
  have h₁ : ((Over.pullback f).map η[A]).left ≫ pullback.fst A.hom f =
      pullback.fst (𝟙_ (Over S)).hom f ≫ η[A].left := pullback.lift_fst _ _ _
  rw [h, Over.comp_left, Category.assoc, h₁, ← Category.assoc]
  congr 1
  have h₂ : pullback.fst (𝟙_ (Over S)).hom f = pullback.snd (𝟙_ (Over S)).hom f ≫ f :=
    (Category.comp_id _).symm.trans pullback.condition
  rw [h₂, ← Category.assoc]
  exact (congrArg (· ≫ f) (Over.w (Functor.LaxMonoidal.ε (Over.pullback f)))).trans
    (Category.id_comp _)
end GlobalTheory.WeightGen
