-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cohomologyPresheafFunctor_map_app_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:07.350126+00:00
-- url     : https://prove2.me/submissions/17f149cc-ac41-40f7-b979-eb4c0a124fd4

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
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G)
    (n : ℕ) (U : C) (x : F.H' n U) :
    ((Sheaf.cohomologyPresheafFunctor J n).map φ).app (op U) x =
      (show Ext (freeSheaf J U) F n from x).comp (Ext.mk₀ φ) (add_zero n) := rfl
end GroundTheory.Arith.SchemeCoh
