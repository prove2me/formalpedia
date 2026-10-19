-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGeometricArithmeticClass.geometricArithmeticClass_actualGenericDiamondHom
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T19:41:07.90917+00:00
-- url     : https://prove2.me/submissions/9be4d72c-36ed-4f55-a055-f0e9cbab60ce

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same existing rational represented Picard has an
intrinsic degree-zero divisor class at every perfect characteristic-zero
field point. The existing rational diamond transports this class by the
actual extension-field diamond. Named downstream consumer: promoting the
arithmetic diamond cyclotomic relation to a scheme morphism identity.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticClassDataExplicitPublicConstructors20261017
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricPointDegreeZeroPresentation_degreeZero_divisor_presentation
import Definitions.Def_MazurTransfer_PicardGeometricFieldPointDegreeZeroConditionData
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_MazurTransfer_presentation_ratio_principal_over_perfect_field

import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_eq_of_presentation
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13ActualPicardGenericFieldAction
open MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle MazurTransfer.Order13ActualPicardGeometricDiamondPresentation
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase)

noncomputable def geometricDiamondChosenPresentation20261017 : ∀ U : (curveScheme K).Opens,
    Γ(actualGeometricPointLineBundle K a, U) →+ actualCurveFunctionField K :=
  (MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 a).choose_spec.choose

theorem geometricDiamondChosenPresentationSpec20261017 :
    IsPresentation (curveToBase K) (actualGeometricPointLineBundle K a)
      (geometricPointDivisor K 𝒱 a).1 (geometricDiamondChosenPresentation20261017 K 𝒱 a) :=
  (MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 a).choose_spec.choose_spec

theorem solution :
    geometricArithmeticClass K 𝒱
        (postComp (actualFieldHom MazurTransfer.Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv) a) =
      (MazurTransfer.Order13FieldDiamondFunctionFieldAutomorphism.diamondAlgEquiv K) •
        geometricArithmeticClass K 𝒱 a := by
  let σ := MazurTransfer.Order13FieldDiamondFunctionFieldAutomorphism.diamondAlgEquiv K
  let E := geometricPointDivisor K 𝒱 a
  obtain ⟨ψ, hψ⟩ := presentation_actualGenericDiamondHom K a E.1
    (geometricDiamondChosenPresentation20261017 K 𝒱 a) (geometricDiamondChosenPresentationSpec20261017 K 𝒱 a)
  have h := geometricArithmeticClass_eq_of_presentation K 𝒱
    (postComp (actualFieldHom MazurTransfer.Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv) a)
    (Pic0.degZeroSMulHom σ E) ψ hψ
  exact h.symm.trans (Pic0.smul_mk σ E).symm


#print axioms solution
