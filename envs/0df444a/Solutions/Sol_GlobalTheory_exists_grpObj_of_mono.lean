-- Prove2me | solution 1 for GlobalTheory.exists_grpObj_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:08.52765+00:00
-- url     : https://prove2.me/submissions/d403ad9f-dd41-47c1-8d82-341bba8d4b62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsGrpObjOfFlatClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
namespace GlobalTheory
theorem _root_.solution {H G : C} [GrpObj G] (j : H ⟶ G) [Mono j]
    (o : 𝟙_ C ⟶ H) (m : H ⊗ H ⟶ H) (n : H ⟶ H) (ho : o ≫ j = η[G])
    (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[G]) (hn : n ≫ j = j ≫ GrpObj.inv) :
    ∃ _ : GrpObj H, IsMonHom j := by
  letI M : MonObj H :=
    { one := o
      mul := m
      one_mul := by
        rw [← cancel_mono j, Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, ho,
          Category.id_comp, tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono j, Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, ho,
          Category.id_comp, MonoidalCategory.tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono j]
        simp only [Category.assoc, hm]
        rw [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          tensorHom_comp_tensorHom_assoc, hm, Category.id_comp]
        have h1 : ((j ⊗ₘ j) ≫ μ[G] ⊗ₘ j) = ((j ⊗ₘ j) ⊗ₘ j) ≫ μ[G] ▷ G := by
          rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
        have h2 : (j ⊗ₘ (j ⊗ₘ j) ≫ μ[G]) = (j ⊗ₘ (j ⊗ₘ j)) ≫ G ◁ μ[G] := by
          rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
        rw [h1, h2, Category.assoc, Category.assoc, MonObj.mul_assoc, associator_naturality_assoc] }
  refine ⟨{ inv := n, left_inv := ?_, right_inv := ?_ }, ⟨ho, hm⟩⟩
  · rw [← cancel_mono j]
    change (lift n (𝟙 H) ≫ m) ≫ j = (toUnit H ≫ o) ≫ j
    rw [Category.assoc, hm, lift_map_assoc, hn, Category.assoc, ho, Category.id_comp]
    have := j ≫= GrpObj.left_inv G
    rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc] at this
    exact this
  · rw [← cancel_mono j]
    change (lift (𝟙 H) n ≫ m) ≫ j = (toUnit H ≫ o) ≫ j
    rw [Category.assoc, hm, lift_map_assoc, hn, Category.assoc, ho, Category.id_comp]
    have := j ≫= GrpObj.right_inv G
    rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc] at this
    exact this
end GlobalTheory
