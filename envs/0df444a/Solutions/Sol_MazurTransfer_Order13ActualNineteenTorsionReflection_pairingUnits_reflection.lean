-- Prove2me | solution 1 for MazurTransfer.Order13ActualNineteenTorsionReflection.pairingUnits_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T21:37:08.649177+00:00
-- url     : https://prove2.me/submissions/ea8b3ff1-0aa6-432d-8687-295984bb2187

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal curve reflection acts on the SAME actual Picard
nineteen-torsion through its intrinsic divisor-class equivalence. It exchanges
the actual norm factors and preserves their actual divisorial pairing.
Named downstream consumer: the one-dimensional kernel of the actual
cyclotomic quotient and its arithmetic character.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
noncomputable section
open MazurTransfer CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualNormKernelProductCardinality
open Order13ActualGeometricNineteenTorsionDivisorComparison Order13ActualNineteenTorsionPairingTransport
open Order13ReflectionParameter Order13FieldPicardReflection Order13ActualNineteenTorsionReflection
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalGroupProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalCommProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalDiamondHomProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalFactProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalAlgebraProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalPiHomProvider20261018
  MazurTransfer.Order13ActualNineteenTorsionReflection.actualReflectionOriginalConjugateHomProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
theorem solution (a : ReflectionParameter K)
    (d : DivisorialWeilPairingData K (actualCurveFunctionField K) 19)
    (x y : NineteenTorsion K) :
    pairingUnits K d (actualReflection K a x) (actualReflection K a y) = pairingUnits K d x y := by
  apply Units.ext
  change d.pair (geometricNineteenTorsionDivisorAddEquiv K (actualReflection K a x))
    (geometricNineteenTorsionDivisorAddEquiv K (actualReflection K a y)) =
      d.pair (geometricNineteenTorsionDivisorAddEquiv K x) (geometricNineteenTorsionDivisorAddEquiv K y)
  rw [actualReflection_class, actualReflection_class]
  convert d.pair_smul (Order13ActualReflectionFunctionField.reflectionAlgEquiv K a)
    (geometricNineteenTorsionDivisorAddEquiv K x) (geometricNineteenTorsionDivisorAddEquiv K y) using 1 <;> rfl

#print axioms solution
