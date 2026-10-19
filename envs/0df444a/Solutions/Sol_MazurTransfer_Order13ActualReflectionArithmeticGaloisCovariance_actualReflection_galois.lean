-- Prove2me | solution 1 for MazurTransfer.Order13ActualReflectionArithmeticGaloisCovariance.actualReflection_galois
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T21:57:58.541456+00:00
-- url     : https://prove2.me/submissions/60211015-5870-4a32-b0b3-e9e0fb046f06

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: reflection covariance for the EXISTING arithmetic Galois
precomposition action on the SAME actual Picard nineteen-torsion.
Named downstream consumer: the reflection-generated line in the actual
cyclotomic quotient kernel, and its arithmetic13 character.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
import Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualArithmeticNineteenTorsionGaloisHomOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Theorems.Thm_MazurTransfer_Order13ActualReflectionCoefficientCovariance_coefficientSemilinearAut_reflection
import Theorems.Thm_MazurTransfer_Order13ActualGeometricGaloisCoefficientComparison_geometricSemilinearAut_eq_coefficient
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricGaloisArithmeticClass_geometricNineteenTorsionDivisorAddEquiv_galois
import Theorems.Thm_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place
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
open Order13ActualReflectionFunctionField Order13ActualReflectionCoefficientCovariance
open Order13ActualGeometricGaloisCoefficientComparison Order13ActualGeometricGaloisSemilinearAutomorphism
open Order13ActualPicardGeometricGaloisArithmeticClass Order13ActualNineteenTorsionGaloisPairingBridge
namespace MazurTransfer.ActualReflectionArithmeticCovarianceProofHelpers20261018
section Generic
universe u v
variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
theorem divisor_action (σ : F ≃ₐ[K] F) (D : Divisor K F) :
    SemilinearAut.ofAlgAut σ • D = σ • D := by
  rw [SemilinearAut.divisor_smul_def, Divisor.smul_def]
  exact congrArg (fun f : Place K F → Place K F => Finsupp.mapDomain f D)
    (funext (SemilinearAut.ofAlgAut_smul_place σ))

theorem pic0_action (σ : F ≃ₐ[K] F) (x : Pic0 K F) :
    SemilinearAut.ofAlgAut σ • x = σ • x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [SemilinearAut.pic0_smul_mk, Pic0.smul_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact divisor_action σ D.val
end Generic
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
theorem reflection_pic0_galois (σ : K ≃ₐ[ℚ] K) (a : ReflectionParameter K)
    (c : Pic0 K (actualCurveFunctionField K)) :
    geometricSemilinearAut K σ • reflection K a c =
      reflection K (mapParameter K σ.toRingEquiv a) (geometricSemilinearAut K σ • c) := by
  change geometricSemilinearAut K σ • (reflectionAlgEquiv K a • c) =
    reflectionAlgEquiv K (mapParameter K σ.toRingEquiv a) • (geometricSemilinearAut K σ • c)
  rw [geometricSemilinearAut_eq_coefficient]
  have h := congrArg (fun f : SemilinearAut K (actualCurveFunctionField K) => f • c)
    (coefficientSemilinearAut_reflection K σ.toRingEquiv a)
  simpa only [mul_smul, pic0_action] using h

end MazurTransfer.ActualReflectionArithmeticCovarianceProofHelpers20261018
open MazurTransfer.ActualReflectionArithmeticCovarianceProofHelpers20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
theorem solution (σ : K ≃ₐ[ℚ] K) (a : ReflectionParameter K)
    (x : NineteenTorsion K) :
    arithmeticNineteenTorsionHom K σ (actualReflection K a x) =
      actualReflection K (mapParameter K σ.toRingEquiv a) (arithmeticNineteenTorsionHom K σ x) := by
  apply (geometricNineteenTorsionDivisorAddEquiv K).injective
  rw [geometricNineteenTorsionDivisorAddEquiv_galois, actualReflection_class,
    actualReflection_class, geometricNineteenTorsionDivisorAddEquiv_galois]
  apply Subtype.ext
  exact reflection_pic0_galois K σ a (geometricNineteenTorsionDivisorAddEquiv K x).val

#print axioms solution
