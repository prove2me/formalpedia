-- Prove2me | solution 1 for GlobalTheory.DualRigidity.rigidity_dualNumber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:51:39.904782+00:00
-- url     : https://prove2.me/submissions/2a53b783-2b9c-4cff-b4b1-6f8c1dce0e87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SubsingletonSpDualNumber
import Theorems.Thm_GlobalTheory_DualRigidity_eq_comp_section_of_const
import Theorems.Thm_GlobalTheory_DualRigidity_subsingleton_sp_dualNumber

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.DualRigidity
namespace GlobalTheory.DualRigidity
theorem _root_.solution : Out.Laws → Out.Laws2 → ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (A' G' : Over (Sp (DualNumber ℂ))) [GrpObj A'] [GrpObj G'] (j : A₀.left ⟶ A'.left) (a b : A' ⟶ G'), IsAbelianScheme A' → IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → j ≫ a.left = j ≫ b.left → η[A'] ≫ a = η[A'] ≫ b → a = b := by
  intro hL _ A₀ _ A' G' _ _ j a b hA hj hab hη
  haveI := subsingleton_sp_dualNumber
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp ℂ) := inferInstance
  let t : Sp (DualNumber ℂ) := spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber ℂ))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber ℂ)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber ℂ))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := eq_comp_section_of_const A'.hom _ c.left hη' (hL.globalFns _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'
end GlobalTheory.DualRigidity
