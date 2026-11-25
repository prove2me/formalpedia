-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.freeSheafHomAddEquiv_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:37.157097+00:00
-- url     : https://prove2.me/submissions/be3c108a-cf54-4e7f-84b3-a6e5c33a9fca

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_freeYonedaHomAddEquiv_apply

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
theorem _root_.solution (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (g : freeSheaf J U ⟶ F) (φ : F ⟶ G) :
    freeSheafHomAddEquiv U G (g ≫ φ) = φ.hom.app (op U) (freeSheafHomAddEquiv U F g) := by
  simp only [freeSheafHomAddEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    freeYonedaHomAddEquiv_apply, Adjunction.homEquiv_naturality_right]
  rfl
end GroundTheory.Arith.SchemeCoh
