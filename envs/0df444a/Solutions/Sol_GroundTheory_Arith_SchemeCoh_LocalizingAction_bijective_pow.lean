-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.LocalizingAction.bijective_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:33.125014+00:00
-- url     : https://prove2.me/submissions/b6c872de-9da5-4709-a303-c4d105ea09bc

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_LocalizingCech

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
open CategoryTheory Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {R : Type u} [CommRing R]
variable {D : R → Opens X} (A : LocalizingAction P D)
open GroundTheory.Arith.SchemeCoh.LocalizingAction
namespace GroundTheory.Arith.SchemeCoh.LocalizingAction
theorem _root_.solution (g : R) (W : Opens X) (hW : W ≤ D g) (L : ℕ) :
    Function.Bijective (A.act (g ^ L) W) := by
  induction L with
  | zero =>
    have : ⇑(A.act (g ^ 0) W) = id := funext fun x => by rw [pow_zero, A.act_one]; rfl
    rw [this]
    exact Function.bijective_id
  | succ L ih =>
    have : ⇑(A.act (g ^ (L + 1)) W) = ⇑(A.act (g ^ L) W) ∘ ⇑(A.act g W) :=
      funext fun x => by rw [pow_succ, A.act_mul]; rfl
    rw [this]
    exact ih.comp (A.bijective g W hW)
end GroundTheory.Arith.SchemeCoh.LocalizingAction
