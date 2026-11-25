-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:10:59.207158+00:00
-- url     : https://prove2.me/submissions/77d0aff5-f83e-4b4b-aa06-65fb3b820c93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Theorems.Thm_GlobalTheory_FieldBaseChange_flat_spMap
import Theorems.Thm_GlobalTheory_FieldBaseChange_surjective_spMap
import Theorems.Thm_GlobalTheory_FieldBaseChange_isMonHom_iff_of_isGrpPullback
import Theorems.Thm_GlobalTheory_FunDescent_app_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.FieldBaseChange
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K), (∀ (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), IsPullback φ p p₀ (spMap i) → Epi φ ∧ Flat φ ∧ Surjective φ ∧ IsAffineHom φ ∧ ∀ U : X₀.Opens, Function.Injective (φ.app U).hom) ∧ ∀ (A₀ B₀ : Over (Sp K₀)) (A B : Over (Sp K)) [GrpObj A₀] [GrpObj B₀] [GrpObj A] [GrpObj B] (φ : A.left ⟶ A₀.left) (ψ : B.left ⟶ B₀.left) (f₀ : A₀ ⟶ B₀) (f : A ⟶ B), IsGrpPullback A A₀ (spMap i) φ → IsGrpPullback B B₀ (spMap i) ψ → φ ≫ f₀.left = f.left ≫ ψ → (IsMonHom f ↔ IsMonHom f₀) := by
  intro K₀ K _ _ i
  have := flat_spMap i
  have := surjective_spMap i
  refine ⟨fun X₀ X p₀ p φ h => ?_, fun A₀ B₀ A B _ _ _ _ φ ψ f₀ f hA hB hf =>
    isMonHom_iff_of_isGrpPullback hA hB f f₀ hf⟩
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip ‹_›
  have : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›
  have : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact ⟨Flat.epi_of_flat_of_surjective φ, ‹_›, ‹_›, ‹_›, fun U => GlobalTheory.FunDescent.app_injective φ U⟩
end GlobalTheory.FieldBaseChange
