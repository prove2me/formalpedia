-- Prove2me | solution 1 for MazurTransfer.Order13ActualReflectionDiamondOrbitAction.actualReflection_fifth
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T23:01:08.208453+00:00
-- url     : https://prove2.me/submissions/bc1fc40e-c7a1-4a47-97b3-3b4a033bc3b6

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: iterating the literal reflection coefficient orbit acts by
corresponding diamond iterates on the SAME actual Picard nineteen-torsion.
Named downstream consumer: the scalar action of the cyclotomic13 generator
on the actual reflected fixed line.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
import Definitions.Def_MazurTransfer_Order13ReflectionDiamondParameterOriginalDataAndConstructorCertificatesMinimalPublicNamespaceV220261018
import Theorems.Thm_MazurTransfer_Order13ActualReflectionDiamondRelation_reflectionAlgEquiv_diamond
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionDiamondComparison_geometricNineteenTorsionDivisorAddEquiv_diamond
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
open Order13ReflectionParameterArithmetic Order13ActualReflectionFunctionField Order13ActualReflectionDiamondRelation
open Order13FieldDiamondPicardEndomorphisms Order13FieldDiamondFunctionFieldAutomorphism
open Order13ActualGeometricNineteenTorsionDiamondComparison
namespace MazurTransfer.ActualReflectionFifthDiamondOrbitProofHelpers20261018
section Generic
universe u
variable {K : Type u} [Field K]
def fifthParameter (a : ReflectionParameter K) : ReflectionParameter K :=
  diamondParameter (diamondParameter (diamondParameter (diamondParameter (diamondParameter a))))

end Generic
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
theorem reflection_next_pic0 (r : ReflectionParameter K) (c : Pic0 K (actualCurveFunctionField K)) :
    reflection K (diamondParameter r) c = reflection K r (rho K c) := by
  change reflectionAlgEquiv K (diamondParameter r) • c = reflectionAlgEquiv K r • (diamondAlgEquiv K • c)
  rw [← reflectionAlgEquiv_diamond, mul_smul]

theorem actualReflection_next (r : ReflectionParameter K) (x : NineteenTorsion K) :
    actualReflection K (diamondParameter r) x = actualReflection K r (actualNineteenTorsionDiamondHom K x) := by
  apply (geometricNineteenTorsionDivisorAddEquiv K).injective
  rw [actualReflection_class, actualReflection_class, geometricNineteenTorsionDivisorAddEquiv_diamond]
  apply Subtype.ext
  exact reflection_next_pic0 K r _

end MazurTransfer.ActualReflectionFifthDiamondOrbitProofHelpers20261018
open MazurTransfer.ActualReflectionFifthDiamondOrbitProofHelpers20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
theorem solution (r : ReflectionParameter K) (x : NineteenTorsion K) :
    actualReflection K (fifthParameter r) x =
      actualReflection K r (((actualNineteenTorsionDiamondHom K : NineteenTorsion K → NineteenTorsion K)^[5]) x) := by
  change actualReflection K (fifthParameter r) x =
    actualReflection K r (actualNineteenTorsionDiamondHom K (actualNineteenTorsionDiamondHom K
      (actualNineteenTorsionDiamondHom K (actualNineteenTorsionDiamondHom K (actualNineteenTorsionDiamondHom K x)))))
  rw [fifthParameter, actualReflection_next, actualReflection_next,
    actualReflection_next, actualReflection_next, actualReflection_next]

#print axioms solution
