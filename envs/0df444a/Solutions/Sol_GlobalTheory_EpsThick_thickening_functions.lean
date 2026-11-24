-- Prove2me | solution 1 for GlobalTheory.EpsThick.thickening_functions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:04:55.544597+00:00
-- url     : https://prove2.me/submissions/430cebbb-2f78-417b-8810-78d0f8785640

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
import Theorems.Thm_GlobalTheory_EpsThick_comb_injective
import Theorems.Thm_GlobalTheory_EpsThick_comb_surjective
import Theorems.Thm_GlobalTheory_EpsThick_isPullback_special
import Theorems.Thm_GlobalTheory_EpsThick_surjective_spMap_fst

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
noncomputable section
open GlobalTheory GlobalTheory.EpsThick
variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {π : Y' ⟶ Sp (DualNumber R)} {ρ : Y' ⟶ Y}
namespace GlobalTheory.EpsThick
theorem _root_.solution : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  intro Y Y' q π ρ j H h₁ h₂
  have P := isPullback_special H h₁ h₂
  refine ⟨fun O => ?_, P, fun O F => ?_⟩
  · have hj : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) P.flip surjective_spMap_fst
    ext x
    obtain ⟨y, rfl⟩ := hj.surj x
    have : ρ (j y) = y := by rw [← Scheme.Hom.comp_apply, h₁]; rfl
    change j (ρ (j y)) ∈ O ↔ j y ∈ O
    rw [this]
  · obtain ⟨ab, hab⟩ := comb_surjective H O F
    exact ⟨ab, hab.symm, fun y hy => comb_injective H O (hy.symm.trans hab.symm)⟩
end GlobalTheory.EpsThick
