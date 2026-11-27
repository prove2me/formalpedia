-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.freeSheafHomAddEquiv_naturality_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:16.828098+00:00
-- url     : https://prove2.me/submissions/fdced5f9-077d-4649-b4ec-48670ed14a3d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_freeYonedaHomAddEquiv_naturality_left

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
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {U V : C} (f : U ⟶ V) (F : Sheaf J AddCommGrpCat.{v})
    (g : freeSheaf J V ⟶ F) :
    freeSheafHomAddEquiv U F (freeSheafMap J f ≫ g) =
      F.obj.map f.op (freeSheafHomAddEquiv V F g) := by
  simp only [freeSheafHomAddEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    Adjunction.homEquiv_naturality_left]
  exact freeYonedaHomAddEquiv_naturality_left f F.obj _
end GroundTheory.Arith.SchemeCoh
