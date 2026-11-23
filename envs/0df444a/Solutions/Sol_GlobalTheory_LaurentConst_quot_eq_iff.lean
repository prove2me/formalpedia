-- Prove2me | solution 1 for GlobalTheory.LaurentConst.quot_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:25.123951+00:00
-- url     : https://prove2.me/submissions/b1cbf54e-0dd9-49d0-8221-1d2b5b48be31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}
namespace GlobalTheory.LaurentConst
theorem _root_.solution (a b : Z ⟶ B.left) (h : b ≫ B.hom = a ≫ B.hom) :
    quot a b h = a ≫ B.hom ≫ (η[B] : 𝟙_ (Over S) ⟶ B).left ↔ a = b := by
  have e : a ≫ B.hom ≫ (η[B] : 𝟙_ (Over S) ⟶ B).left = (1 : Over.mk (a ≫ B.hom) ⟶ B).left := by
    rw [Hom.one_def, Over.comp_left, ← Category.assoc]; rfl
  rw [e]
  refine ⟨fun H ↦ congrArg (·.left) (mul_inv_eq_one.1 (Over.OverMorphism.ext H)), ?_⟩
  rintro rfl
  rw [quot, mul_inv_cancel]
end GlobalTheory.LaurentConst
