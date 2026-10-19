-- Prove2me | solution 1 for MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison.geometricTorsionClassHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T11:04:26.479998+00:00
-- url     : https://prove2.me/submissions/5dfebec4-e326-404b-aac3-a356375b4970

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: existence of an auxiliary additive arithmetic Picard
comparison for the SAME actual rational Picard, using the accepted
underlying arithmetic correspondence directly.
Named downstream consumer: surjectivity of the natural nineteen-torsion
divisor-class map. No equality with a chosen comparison map is asserted.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardAlgPointsComparisonData20261018
import Definitions.Def_MazurTransfer_Order13ActualRationalFunctionFieldTowerOriginalInstancesDataV220261018
import Theorems.Thm_MazurTransfer_Order13IntegralPicardLiteralFibreRelativeGroupCompatibility_literal_fibre_relative_group_compatibility
import Theorems.Thm_MazurTransfer_PicardRepresentationPointComparison_overPointEquiv_mul
import Theorems.Thm_MazurTransfer_order13_actual_arithmetic_picard_group_equivalence
import Definitions.Def_MazurTransfer_Order13ActualGeometricNineteenTorsionNaturalDivisorMapOriginalFieldContextDataV320261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelProductCardinality_nineteenTorsion_finite
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticGroup_geometricArithmeticClassOver_injective_explicitOriginalType20261017
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13IntegralSections
open MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations
open MazurTransfer.Order13IntegralPicardLiteralFibreRelativeGroupCompatibility
open MazurTransfer.PicardRepresentationPointComparison
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGeometricNormPreimages
open Order13ActualNormKernelProductCardinality Order13ActualPicardAlgPointsComparison
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018
attribute [local instance] Order13ActualRationalFunctionFieldTower.actualRatFuncTowerOriginalFactProvider20261018 Order13ActualRationalFunctionFieldTower.actualRatFuncTowerOriginalAlgebraProvider20261018

open Order13ActualGeometricNineteenTorsionDivisorComparison
attribute [local instance] naturalDivisorMapOriginalFactProvider20261018 naturalDivisorMapOriginalAlgebraProvider20261018

private theorem auxiliaryArithmeticClassAddEquivExistsOriginalProof20261018 (K : Type) [Field K] [CharZero K] :
    Nonempty (Additive (Points K) ≃+ Pic0 K (actualCurveFunctionField K)) := by
  let R := ℚ
  let D := actualPicard
  let h := actualRepresentation
  have h104 : IsUnit (104 : R) := by norm_num [R]
  letI := actualLaw.pointGroup (specMap ℚ K)
  have e : Nonempty (SchemeHomOver (specMap R K) D.toBase ≃*
      Multiplicative (Pic0 K (actualCurveFunctionField K))) := by
    have hh : IsUnit (104 : K) := by simpa only [map_ofNat] using h104.map (algebraMap R K)
    letI : Fact ((104 : K) ≠ 0) := ⟨hh.ne_zero⟩
    letI := (show RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroGroupCut (curveToBase R) (positiveInfinitySection R)).toSubPicCondition
        D from h).relativeGroupLaw.pointGroup (specMap R K)
    obtain ⟨hK,hΘ⟩ := literal_fibre_relative_group_compatibility R K D h
    let hKG : RepresentsRelSubPic (curveToBase K) (positiveInfinitySection K)
        (algEquivZeroGroupCut (curveToBase K) (positiveInfinitySection K)).toSubPicCondition
        (literalFibreDesignation R K D) := hK
    letI := hKG.grpObj
    obtain ⟨Θ,_,hmul⟩ := hΘ
    let ΘG : (Over.mk (𝟙 (Spec (.of K))) ⟶ Over.mk (literalFibreDesignation R K D).toBase) ≃*
        SchemeHomOver (specMap R K) D.toBase := { Θ with map_mul' := hmul }
    obtain ⟨D0,h0,⟨A⟩⟩ := MazurTransfer.order13_actual_arithmetic_picard_group_equivalence
      K hh.ne_zero (positiveInfinitySection K)
    let h0G : RepresentsRelSubPic (curveToBase K) (positiveInfinitySection K)
        (algEquivZeroGroupCut (curveToBase K) (positiveInfinitySection K)).toSubPicCondition D0 := h0
    letI := h0G.grpObj
    let E : (Over.mk (𝟙 (Spec (.of K))) ⟶ Over.mk (literalFibreDesignation R K D).toBase) ≃*
        (Over.mk (𝟙 (Spec (.of K))) ⟶ Over.mk D0.toBase) :=
      { overPointEquiv hK h0 (𝟙 _) with
        map_mul' := by
          intro a b
          exact overPointEquiv_mul
            (P := algEquivZeroGroupCut (curveToBase K) (positiveInfinitySection K)) hKG h0G a b }
    exact ⟨ΘG.symm.trans (E.trans A)⟩
  let a : actualLaw.AlgPoints actualLaw_isCommutative K ≃+ Pic0 K (actualCurveFunctionField K) :=
    AddEquiv.ofBijective e.some.toMonoidHom.toAdditiveLeft e.some.bijective
  exact ⟨(actualAlgPointsAddEquiv K).trans a⟩


theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Function.Surjective (geometricTorsionClassHom K) := by
  letI : Finite (NineteenTorsion K) := nineteenTorsion_finite K
  let a := (auxiliaryArithmeticClassAddEquivExistsOriginalProof20261018 K).some
  let e : NineteenTorsion K ≃ Pic0.torsion K (actualCurveFunctionField K) 19 :=
    Equiv.subtypeEquiv a.toEquiv (by
      intro x
      change (19 : ℕ) • x = 0 ↔ (19 : ℤ) • a x = 0
      erw [natCast_zsmul, ← map_nsmul a]
      constructor
      · intro hx
        rw [hx, map_zero]
      · intro hx
        apply a.injective
        simpa only [map_zero] using hx)
  have hi : Function.Injective (geometricTorsionClassHom K) := by
    intro x y hxy
    apply Subtype.ext
    exact Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_injective_explicitOriginalType20261017
      K (GoodCharacteristicGeometryPublicProof.MazurTorsion.XOneThirteenProjectiveCurve.actualTwoAffineOpenCover K)
      (congrArg Subtype.val hxy)
  have hs := Finite.surjective_of_injective
    (f := fun x => e.symm (geometricTorsionClassHom K x))
    (e.symm.injective.comp hi)
  intro y
  obtain ⟨x, hx⟩ := hs (e.symm y)
  exact ⟨x, e.symm.injective hx⟩

#print axioms solution
