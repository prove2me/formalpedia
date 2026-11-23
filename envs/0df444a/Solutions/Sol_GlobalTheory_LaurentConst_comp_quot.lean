-- Prove2me | solution 1 for GlobalTheory.LaurentConst.comp_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:44.955428+00:00
-- url     : https://prove2.me/submissions/1b52d819-c633-4791-9309-3054ba5c93ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}
namespace GlobalTheory.LaurentConst
theorem _root_.solution (j : W ⟶ Z) (a b : Z ⟶ B.left) (h : b ≫ B.hom = a ≫ B.hom) :
    j ≫ quot a b h = quot (j ≫ a) (j ≫ b) (by simp [h]) := by
  let j' : Over.mk ((j ≫ a) ≫ B.hom) ⟶ Over.mk (a ≫ B.hom) := Over.homMk j (by simp)
  have : j' ≫ ((Over.homMk a rfl : Over.mk (a ≫ B.hom) ⟶ B) *
      (Over.homMk b h : Over.mk (a ≫ B.hom) ⟶ B)⁻¹) =
      (Over.homMk (j ≫ a) rfl) * (Over.homMk (j ≫ b) (by simp [h]))⁻¹ := by
    rw [MonObj.comp_mul, GrpObj.comp_inv]; rfl
  exact congrArg (·.left) this
end GlobalTheory.LaurentConst
