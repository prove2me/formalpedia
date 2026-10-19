-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGeometricGaloisArithmeticClass.geometricArithmeticClassOver_galois
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T14:33:30.336716+00:00
-- url     : https://prove2.me/submissions/93b5b396-f0bd-4099-bd3a-b01348f4182e

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the intrinsic divisor-class map of the SAME represented
rational Picard intertwines its existing Galois precomposition action with
the semilinear action induced by the actual curve Galois isomorphism.
Named downstream consumer: unconditional Galois covariance of the actual
nineteen pairing and the arithmetic character exact sequences.
-/
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricPointDegreeZeroPresentation_degreeZero_divisor_presentation
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_eq_of_presentation
import Theorems.Thm_MazurTransfer_Order13ActualGaloisDivisorPresentationPullback_presentation_galois_pullback
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricGaloisLineBundle_actualGeometricPointLineBundle_galois_iso_pullback
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticGroupData
import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualNormKernelProductCardinality
open Order13ActualPicardNormKernelGaloisAction Order13ActualPicardGeometricArithmeticGroup
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardGeometricPointDegreeZeroPresentation Order13ActualPicardGeometricArithmeticClass
open Order13ActualPicardGeometricDiamondLineBundle Order13ActualPicardGeometricGaloisLineBundle
open Order13ActualGeometricGaloisSemilinearAutomorphism Order13ActualGaloisDivisorPresentationPullback
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
    (𝒱 : (curveScheme K).TwoAffineOpenCover) (σ : K ≃ₐ[ℚ] K) (a : Points K) :
    geometricArithmeticClassOver K 𝒱 (actionHom K σ a) =
      geometricSemilinearAut K σ • geometricArithmeticClassOver K 𝒱 a := by
  obtain ⟨E, φ, hE⟩ := degreeZero_divisor_presentation K 𝒱 (pointOfOverHom K a)
  have ha : Pic0.mk E = geometricArithmeticClassOver K 𝒱 a :=
    geometricArithmeticClass_eq_of_presentation K 𝒱 (pointOfOverHom K a) E φ hE
  obtain ⟨ψ, hψ⟩ := presentation_galois_pullback K σ
    (actualGeometricPointLineBundle K (pointOfOverHom K a)) E.val φ hE
  obtain ⟨i⟩ := actualGeometricPointLineBundle_galois_iso_pullback K σ a
  have ht := geometricArithmeticClass_eq_of_presentation K 𝒱
    (pointOfOverHom K (actionHom K σ a))
    (SemilinearAut.degZeroSMulHom (geometricSemilinearAut K σ) E)
    (fun U => (ψ U).comp (Scheme.Modules.Hom.app i.hom U).hom)
    (IsPresentation.of_iso i hψ)
  calc
    geometricArithmeticClassOver K 𝒱 (actionHom K σ a) =
      Pic0.mk (SemilinearAut.degZeroSMulHom (geometricSemilinearAut K σ) E) := ht.symm
    _ = geometricSemilinearAut K σ • Pic0.mk E := (SemilinearAut.pic0_smul_mk _ E).symm
    _ = geometricSemilinearAut K σ • geometricArithmeticClassOver K 𝒱 a := congrArg (_ • ·) ha

#print axioms solution
