-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.freeYonedaHomAddEquiv_naturality_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:11.248806+00:00
-- url     : https://prove2.me/submissions/1fe5dffa-8e3f-4487-96f7-2a99743f4c8e

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Limits Opposite Abelian
universe w' v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {U V : C} (f : U ⟶ V) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (g : yoneda.obj V ⋙ AddCommGrpCat.free.{v} ⟶ P) :
    freeYonedaHomAddEquiv U P (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free ≫ g) =
      P.map f.op (freeYonedaHomAddEquiv V P g) := by
  change yonedaEquiv (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) P)
      (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map f) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  have := NatTrans.naturality_apply
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj V) P) g) f.op (𝟙 V)
  exact (congrArg _ (Category.comp_id f).symm).trans this
end GroundTheory.Arith.SchemeCoh
