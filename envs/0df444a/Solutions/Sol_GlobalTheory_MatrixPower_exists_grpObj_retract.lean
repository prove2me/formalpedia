-- Prove2me | solution 1 for GlobalTheory.MatrixPower.exists_grpObj_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:54:26.375473+00:00
-- url     : https://prove2.me/submissions/9b78b19e-6c65-44a9-b872-818e6e3bde59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AbelianSchemeEighthPowerOfMatrixAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.MatrixPower
section General
variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
private theorem isMonHom_of_one_comp_of_mul_comp {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N)
    (h1 : (1 : 𝟙_ C ⟶ M) ≫ f = 1)
    (h2 : (fst M M * snd M M) ≫ f = fst M M ≫ f * snd M M ≫ f) : IsMonHom f :=
  { one_hom := by rw [MonObj.one_eq_one M, MonObj.one_eq_one N, h1]
    mul_hom := by
      rw [MonObj.mul_eq_mul M, MonObj.mul_eq_mul N, h2, MonObj.comp_mul, tensorHom_fst,
        tensorHom_snd] }
variable [BraidedCategory C]
end General
end GlobalTheory.MatrixPower
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.MatrixPower
variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
namespace GlobalTheory.MatrixPower
theorem _root_.solution {G A : C} [GrpObj G] (i : A ⟶ G) (r : G ⟶ A) (hir : i ≫ r = 𝟙 A)
    [he : IsMonHom (r ≫ i)] : ∃ _ : GrpObj A, IsMonHom i ∧ IsMonHom r := by
  let gA : GrpObj A := retractGrpObj i r hir
  have hm : ∀ {T : C} (a b : T ⟶ A), a * b = (a ≫ i * b ≫ i) ≫ r := by
    intro T a b
    rw [Hom.mul_def]
    change lift a b ≫ (fst A A ≫ i * snd A A ≫ i) ≫ r = _
    rw [← Category.assoc, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  have ho : ∀ {T : C}, (1 : T ⟶ A) = (1 : T ⟶ G) ≫ r := by
    intro T
    rw [Hom.one_def]
    change toUnit T ≫ (1 : 𝟙_ C ⟶ G) ≫ r = _
    rw [← Category.assoc, MonObj.comp_one]
  refine ⟨gA, ?_, ?_⟩
  · refine isMonHom_of_one_comp_of_mul_comp i ?_ ?_
    · rw [ho, Category.assoc, MonObj.one_comp]
    · rw [hm, Category.assoc, MonObj.mul_comp]
      simp only [Category.assoc, reassoc_of% hir]
  · refine isMonHom_of_one_comp_of_mul_comp r ho.symm ?_
    rw [hm]
    calc (fst G G * snd G G) ≫ r = ((fst G G * snd G G) ≫ (r ≫ i)) ≫ r := by
          simp only [Category.assoc, hir, Category.comp_id]
      _ = _ := by rw [MonObj.mul_comp]; simp only [Category.assoc]
end GlobalTheory.MatrixPower
