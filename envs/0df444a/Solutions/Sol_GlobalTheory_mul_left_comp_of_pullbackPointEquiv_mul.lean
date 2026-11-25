-- Prove2me | solution 1 for GlobalTheory.mul_left_comp_of_pullbackPointEquiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:33.30165+00:00
-- url     : https://prove2.me/submissions/1045cfd1-0bad-4e93-a007-68470bb5de87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory
variable {S S' : Scheme.{u}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
namespace GlobalTheory
theorem _root_.solution [GrpObj G] [GrpObj G']
    (h : IsPullback φ G'.hom G.hom f) {T' : Over S'} {T : Over S} (t : T'.left ⟶ T.left)
    {x' y' : T' ⟶ G'} {x y : T ⟶ G}
    (hm : pullbackPointEquiv h T' (x' * y') =
      pullbackPointEquiv h T' x' * pullbackPointEquiv h T' y')
    (hx : x'.left ≫ φ = t ≫ x.left) (hy : y'.left ≫ φ = t ≫ y.left) :
    (x' * y').left ≫ φ = t ≫ (x * y).left := by
  rw [← pullbackPointEquiv_apply_left h, hm, Hom.mul_def, Hom.mul_def,
    Over.comp_left, Over.comp_left, ← Category.assoc]
  congr 1
  ext
  · rw [Category.assoc]
    change (lift (pullbackPointEquiv h T' x') (pullbackPointEquiv h T' y') ≫ fst G G).left = t ≫ (lift x y ≫ fst G G).left
    rw [lift_fst, lift_fst, pullbackPointEquiv_apply_left, hx]
  · rw [Category.assoc]
    change (lift (pullbackPointEquiv h T' x') (pullbackPointEquiv h T' y') ≫ snd G G).left = t ≫ (lift x y ≫ snd G G).left
    rw [lift_snd, lift_snd, pullbackPointEquiv_apply_left, hy]
end GlobalTheory
