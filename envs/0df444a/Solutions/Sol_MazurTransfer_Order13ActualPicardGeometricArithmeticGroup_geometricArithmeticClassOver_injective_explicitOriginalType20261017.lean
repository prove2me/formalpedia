-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_injective_explicitOriginalType20261017
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T20:28:18.327219+00:00
-- url     : https://prove2.me/submissions/a0f6d174-d041-4dee-ac74-1170df074eb9

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric arithmetic group map on points of the
same existing rational represented Picard is injective. Named downstream
consumer: detection of the actual diamond cyclotomic and scheme norm identities.
Complete original MazurTheorem geometric arithmetic group proof;
official Anthropic FLT Poincare identity inputs at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondGroupActionExplicitConstructorFacts20261017
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Theorems.Thm_MazurTransfer_PicardGeometricFieldPointLineBundleInjectivity_geometricPointLineBundle_iso_iff
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open MazurTransfer.Order13ActualPicardGeometricArithmeticGroup
open MazurTransfer.Order13GeometricRelativeCurveChange
open scoped CategoryTheory.MonObj
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)

namespace MazurTransfer.GeometricArithmeticGroupInjectivityHelpers20261017
theorem geometricPointLineBundle_over_one_iso_unit :
    letI := (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
      (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
    Nonempty (actualGeometricPointLineBundle K (pointOfOverHom K 1) ≅
      𝟙_ (curveScheme K).Modules) := by
  let hG : RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard := actualRepresentation
  letI := hG.grpObj
  obtain ⟨i⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso hG
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))))
  exact ⟨(Scheme.Modules.pullback (geometricCurveEmbedding K)).mapIso i ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (geometricCurveEmbedding K)⟩

theorem geometricArithmeticClassOver_one :
    letI := (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
      (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
    geometricArithmeticClassOver K 𝒱 1 = 0 := by
  letI := (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
  exact (MazurTransfer.Order13ActualPicardGeometricArithmeticKernel.geometricArithmeticClass_eq_zero_iff_lineBundle_iso_unit K 𝒱 _).mpr
    (geometricPointLineBundle_over_one_iso_unit K)

theorem geometricArithmeticClassOver_eq_zero_iff_eq_one :
    letI := (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
      (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
    ∀ a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase,
      geometricArithmeticClassOver K 𝒱 a = 0 ↔ a = 1 := by
  letI := (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
  intro a
  constructor
  · intro ha
    obtain ⟨ia⟩ := (MazurTransfer.Order13ActualPicardGeometricArithmeticKernel.geometricArithmeticClass_eq_zero_iff_lineBundle_iso_unit K 𝒱 _).mp ha
    obtain ⟨i1⟩ := geometricPointLineBundle_over_one_iso_unit K
    have hp := (MazurTransfer.PicardGeometricFieldPointLineBundleInjectivity.geometricPointLineBundle_iso_iff (curveToBase ℚ) infinitySection actualPicard actualRepresentation
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (geometricCurveEmbedding K)
      (pointOfOverHom K a) (pointOfOverHom K 1)).mp ⟨ia ≪≫ i1.symm⟩
    exact Over.OverMorphism.ext (congrArg Subtype.val hp)
  · rintro rfl
    exact geometricArithmeticClassOver_one K 𝒱

end MazurTransfer.GeometricArithmeticGroupInjectivityHelpers20261017
open MazurTransfer.GeometricArithmeticGroupInjectivityHelpers20261017
theorem solution : Function.Injective (geometricArithmeticClassOver K 𝒱) := by
  letI := (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
  intro a b hab
  have h4 : geometricArithmeticClassOver K 𝒱 (b * b⁻¹) = 0 := by
    rw [mul_inv_cancel, geometricArithmeticClassOver_one K 𝒱]
  have h3 : geometricArithmeticClassOver K 𝒱 (a * b⁻¹) = 0 := by
    rw [geometricArithmeticClassOver_mul K 𝒱] at h4 ⊢
    rw [hab]
    exact h4
  have h1 := (geometricArithmeticClassOver_eq_zero_iff_eq_one K 𝒱 _).mp h3
  exact mul_inv_eq_one.mp h1


#print axioms solution
