-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGeometricGaloisArithmeticClass.geometricNineteenTorsionDivisorAddEquiv_galois
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T14:42:24.71276+00:00
-- url     : https://prove2.me/submissions/6bcc4bc3-5bc4-4a94-adbf-76c80676b24f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the intrinsic divisor-class map of the SAME represented
rational Picard intertwines its existing Galois precomposition action with
the semilinear action induced by the actual curve Galois isomorphism.
Named downstream consumer: unconditional Galois covariance of the actual
nineteen pairing and the arithmetic character exact sequences.
-/
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricGaloisArithmeticClass_geometricArithmeticClassOver_galois
import Definitions.Def_MazurTransfer_Order13ActualArithmeticNineteenTorsionGaloisHomOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNaturalNineteenTorsionDivisorAddEquivData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardGeometricNormPreimages Order13ActualNormKernelProductCardinality
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricArithmeticGroup
open Order13ActualGeometricNineteenTorsionDivisorComparison
open Order13ActualPicardGeometricGaloisArithmeticClass Order13ActualNineteenTorsionGaloisPairingBridge
open Order13ActualGeometricGaloisSemilinearAutomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
    (σ : K ≃ₐ[ℚ] K) (x : NineteenTorsion K) :
    geometricNineteenTorsionDivisorAddEquiv K (arithmeticNineteenTorsionHom K σ x) =
      geometricSemilinearAut K σ • geometricNineteenTorsionDivisorAddEquiv K x := by
  apply Subtype.ext
  change geometricArithmeticClassOver K
    (GoodCharacteristicGeometryPublicProof.MazurTorsion.XOneThirteenProjectiveCurve.actualTwoAffineOpenCover K)
    (actionHom K σ x.val.toMul) = _
  exact geometricArithmeticClassOver_galois K _ σ x.val.toMul

#print axioms solution
