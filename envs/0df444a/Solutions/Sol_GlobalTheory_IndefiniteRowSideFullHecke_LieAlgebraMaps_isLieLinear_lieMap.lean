-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.isLieLinear_lieMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:52:34.121877+00:00
-- url     : https://prove2.me/submissions/0fe347a8-43e0-46a7-821b-cb101d1ef2ac

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LieAlgebraMaps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps
namespace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps
theorem _root_.solution {R : Type} [CommRing R] {T G : Over (Spec (CommRingCat.of R))}
    [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u] : IsLieLinear (lieMap u) :=
  ⟨fun x y => Subtype.ext (MonObj.mul_comp x.1 y.1 u),
    fun a x => Subtype.ext (Category.assoc _ _ _)⟩
end GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps
