-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.freeYonedaHomAddEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:10.583653+00:00
-- url     : https://prove2.me/submissions/c22aa0da-9009-4cfd-ac54-2fadb4d05acd

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
theorem _root_.solution (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (g : yoneda.obj U ⋙ AddCommGrpCat.free.{v} ⟶ P) :
    freeYonedaHomAddEquiv U P g = g.app (op U) (FreeAbelianGroup.of (𝟙 U)) := rfl
end GroundTheory.Arith.SchemeCoh
