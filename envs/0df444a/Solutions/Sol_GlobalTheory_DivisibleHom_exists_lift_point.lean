-- Prove2me | solution 1 for GlobalTheory.DivisibleHom.exists_lift_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:57.093535+00:00
-- url     : https://prove2.me/submissions/956f134e-3868-4789-8a30-f9ed8e1d9232

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsEqPowOfTorsionCompEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DivisibleHom
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
namespace GlobalTheory.DivisibleHom
namespace _root_.GlobalTheory.DivisibleHom
theorem _root_.solution {A A' T : Over S} (m : A' ⟶ A) [Flat m.left]
    [Surjective m.left] (y : T ⟶ A) :
    ∃ (T' : Over S) (e : T' ⟶ T) (x : T' ⟶ A'), Flat e.left ∧ Surjective e.left ∧
      x ≫ m = e ≫ y := by
  refine ⟨Over.mk (pullback.snd m.left y.left ≫ T.hom), Over.homMk (pullback.snd m.left y.left) rfl,
    Over.homMk (pullback.fst m.left y.left) ?_, ?_, ?_, ?_⟩
  · show pullback.fst m.left y.left ≫ A'.hom = pullback.snd m.left y.left ≫ T.hom
    rw [← Over.w m, ← Category.assoc, pullback.condition, Category.assoc, Over.w y]
  · show Flat (pullback.snd m.left y.left)
    infer_instance
  · show Surjective (pullback.snd m.left y.left)
    infer_instance
  · ext1
    simp [pullback.condition]
end _root_.GlobalTheory.DivisibleHom
end GlobalTheory.DivisibleHom
