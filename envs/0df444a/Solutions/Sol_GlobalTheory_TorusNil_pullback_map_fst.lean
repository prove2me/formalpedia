-- Prove2me | solution 1 for GlobalTheory.TorusNil.pullback_map_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:47.25123+00:00
-- url     : https://prove2.me/submissions/daaa11e7-e08e-4280-8da0-d9c3446b27b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
namespace GlobalTheory.TorusNil
theorem _root_.solution {S S' : Scheme.{0}} {p : S' ⟶ S} {Z : Over S'} {V W : Over S}
    (u : Z ⟶ (Over.pullback p).obj V) (f : V ⟶ W) :
    (u ≫ (Over.pullback p).map f).left ≫ pullback.fst W.hom p =
      u.left ≫ pullback.fst V.hom p ≫ f.left := by
  rw [Over.comp_left]
  refine (Category.assoc _ _ _).trans (congrArg (u.left ≫ ·) ?_)
  exact pullback.lift_fst _ _ _
end GlobalTheory.TorusNil
