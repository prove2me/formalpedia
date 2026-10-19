-- Prove2me | solution 1 for MazurTransfer.Order13ActualNineteenPairingGaloisCovariance.actualPairing_galois
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T14:53:52.030885+00:00
-- url     : https://prove2.me/submissions/18497f59-1fa5-4485-b520-8dd9ed79d8ed

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the existing precomposition arithmetic Galois action on
SAME actual Picard nineteen torsion makes its chosen actual divisorial
pairing covariant for the literal field action on units.
Named downstream consumer: cyclotomic quotients of the actual norm-kernel
representations, arithmetic character exact sequences and Selmer bounds.
-/
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricGaloisArithmeticClass_geometricNineteenTorsionDivisorAddEquiv_galois
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_semilinearSmul
import Definitions.Def_MazurTransfer_Order13ActualArithmeticNineteenTorsionGaloisHomOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionPairingTransportOriginalData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualNormKernelProductCardinality Order13ActualNineteenTorsionGaloisPairingBridge
open Order13ActualPicardGeometricGaloisArithmeticClass
open Order13ActualGeometricNineteenTorsionDivisorComparison
open Order13ActualNineteenTorsionPairingTransport Order13ActualGeometricNineteenDivisorialPairing
open Order13ActualGeometricGaloisSemilinearAutomorphism
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018
attribute [local instance] geometricGaloisOriginalFactProvider20261018 geometricGaloisOriginalAlgebraProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (x y : NineteenTorsion K) :
    actualGeometricNineteenPairing K (arithmeticNineteenTorsionHom K σ x)
      (arithmeticNineteenTorsionHom K σ y) =
      Units.map σ.toRingHom.toMonoidHom (actualGeometricNineteenPairing K x y) := by
  apply Units.ext
  change (actualDivisorialNineteenPairingData K).pair
    (geometricNineteenTorsionDivisorAddEquiv K (arithmeticNineteenTorsionHom K σ x))
    (geometricNineteenTorsionDivisorAddEquiv K (arithmeticNineteenTorsionHom K σ y)) = _
  rw [geometricNineteenTorsionDivisorAddEquiv_galois,
    geometricNineteenTorsionDivisorAddEquiv_galois]
  exact (actualDivisorialNineteenPairingData K).pair_semilinearSmul _ _ _

#print axioms solution
