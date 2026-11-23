-- Prove2me | solution 1 for GlobalTheory.ReducedSubgroup.exists_grpObj_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:21.801196+00:00
-- url     : https://prove2.me/submissions/90587666-5866-4802-a9e5-e22b679dfef9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField

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
open GlobalTheory GlobalTheory.ReducedSubgroup
variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞]
namespace GlobalTheory.ReducedSubgroup
theorem _root_.solution {N B : 𝒞} [GrpObj B] (ν : N ⟶ B) [Mono ν] (e : 𝟙_ 𝒞 ⟶ N)
    (m : N ⊗ N ⟶ N) (i : N ⟶ N) (he : e ≫ ν = η[B]) (hm : m ≫ ν = (ν ⊗ₘ ν) ≫ μ[B])
    (hi : i ≫ ν = ν ≫ GrpObj.inv) : ∃ _ : GrpObj N, IsMonHom ν := by
  have hl : ∀ {T : 𝒞} (a b : T ⟶ N), lift a b ≫ m ≫ ν = (a ≫ ν) * (b ≫ ν) := by
    intro T a b
    rw [hm, lift_map_assoc, Hom.mul_def]
  have hm' : m ≫ ν = (fst N N ≫ ν) * (snd N N ≫ ν) := by
    rw [← hl, lift_fst_snd, Category.id_comp]
  have he' : ∀ {T : 𝒞} (a : T ⟶ 𝟙_ 𝒞), a ≫ e ≫ ν = 1 := by
    intro T a
    rw [he, Hom.one_def, toUnit_unique a (toUnit T)]
  have hi' : i ≫ ν = ν⁻¹ := by rw [hi, Hom.inv_def]
  letI M : MonObj N :=
    { one := e
      mul := m
      one_mul := by
        rw [← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerRight_fst_assoc,
          whiskerRight_snd_assoc, he', _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono ν, Category.assoc, hm', comp_mul, whiskerLeft_fst_assoc,
          whiskerLeft_snd_assoc, he', _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono ν]
        simp only [Category.assoc]
        conv_lhs => rw [hm', comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc, hm',
          comp_mul]
        conv_rhs => rw [hm', comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hm',
          comp_mul, comp_mul, comp_mul]
        simp [_root_.mul_assoc] }
  refine ⟨{ inv := i, left_inv := ?_, right_inv := ?_ }, ⟨he, hm⟩⟩
  · rw [← cancel_mono ν, Category.assoc, Category.assoc]
    exact (hl i (𝟙 N)).trans (by rw [hi', Category.id_comp, inv_mul_cancel]; exact (he' _).symm)
  · rw [← cancel_mono ν, Category.assoc, Category.assoc]
    exact (hl (𝟙 N) i).trans (by rw [hi', Category.id_comp, mul_inv_cancel]; exact (he' _).symm)
end GlobalTheory.ReducedSubgroup
