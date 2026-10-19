-- Prove2me | solution 1 for MazurTransfer.order13_actual_nineteen_torsion_reflection_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T21:42:39.663605+00:00
-- url     : https://prove2.me/submissions/7d67fee8-b0df-4e91-b1eb-cbd83065fcc4

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: exact original norm-exchange identities on the same represented nineteen-torsion.
Named downstream consumer: Order13ActualReflectionPairingOrthogonality.restrictedKernelReflection. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionReflectionOriginalAdditiveEquivalencesAndClassCertificate20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionDiamondOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionDiamondComparison_geometricNineteenTorsionDivisorAddEquiv_diamond
import Theorems.Thm_MazurTransfer_order13_field_picard_reflection_norm_certificates
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
open Order13ActualNineteenTorsionNormPairingAdjoint Order13ActualPicardSchemeNineteenNorm
open Order13ActualGeometricNineteenTorsionDiamondComparison Order13FieldDiamondPicardEndomorphisms
open Order13ActualPicardGeometricDiamondGroupAction
namespace MazurTransfer.ActualNineteenTorsionReflectionNormProofHelpers20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
theorem normPi_apply (x : NineteenTorsion K) :
    actualNineteenTorsionNormHom K schemePi x =
      (3 : ℕ) • x + (2 : ℕ) • actualNineteenTorsionDiamondHom K x := by
  apply Subtype.ext
  change (x.val.toMul ≫ schemePi) = x.val.toMul ^ 3 * (x.val.toMul ≫ schemeDiamond) ^ 2
  simp only [schemePi, MonObj.comp_mul, MonObj.comp_pow, Category.comp_id]

theorem normPiConjugate_apply (x : NineteenTorsion K) :
    actualNineteenTorsionNormHom K schemePiConjugate x =
      (5 : ℕ) • x - (2 : ℕ) • actualNineteenTorsionDiamondHom K x := by
  apply Subtype.ext
  change (x.val.toMul ≫ schemePiConjugate) =
    x.val.toMul ^ 5 * ((x.val.toMul ≫ schemeDiamond) ^ 2)⁻¹
  simp only [schemePiConjugate, MonObj.comp_mul, MonObj.comp_pow, GrpObj.comp_inv, Category.comp_id]

theorem actualReflection_involution (a : ReflectionParameter K) (x : NineteenTorsion K) :
    actualReflection K a (actualReflection K a x) = x := by
  apply (geometricNineteenTorsionDivisorAddEquiv K).injective
  rw [actualReflection_class, actualReflection_class]
  apply Subtype.ext
  change Order13ActualReflectionFunctionField.reflectionAlgEquiv K a •
    (Order13ActualReflectionFunctionField.reflectionAlgEquiv K a •
      (geometricNineteenTorsionDivisorAddEquiv K x).val) = _
  rw [← mul_smul, MazurTransfer.ReflectionPicardConstructorProofHelpers20261018.reflectionAlgEquiv_square K a, one_smul]

theorem actualReflection_normPi (a : ReflectionParameter K) (x : NineteenTorsion K) :
    actualReflection K a (actualNineteenTorsionNormHom K schemePi x) =
      actualNineteenTorsionNormHom K schemePiConjugate (actualReflection K a x) := by
  apply (geometricNineteenTorsionDivisorAddEquiv K).injective
  apply Subtype.ext
  have hp (z : NineteenTorsion K) :
      (geometricNineteenTorsionDivisorAddEquiv K (actualNineteenTorsionNormHom K schemePi z)).val =
        pi K (geometricNineteenTorsionDivisorAddEquiv K z).val := by
    rw [normPi_apply, map_add, map_nsmul, map_nsmul,
      geometricNineteenTorsionDivisorAddEquiv_diamond]
    rfl
  have hc (z : NineteenTorsion K) :
      (geometricNineteenTorsionDivisorAddEquiv K (actualNineteenTorsionNormHom K schemePiConjugate z)).val =
        piConjugate K (geometricNineteenTorsionDivisorAddEquiv K z).val := by
    rw [normPiConjugate_apply, map_sub, map_nsmul, map_nsmul,
      geometricNineteenTorsionDivisorAddEquiv_diamond]
    rfl
  have hr (z : NineteenTorsion K) :
      (geometricNineteenTorsionDivisorAddEquiv K (actualReflection K a z)).val =
        reflection K a (geometricNineteenTorsionDivisorAddEquiv K z).val := by
    exact congrArg Subtype.val (actualReflection_class K a z)
  rw [hr, hp, hc, hr]
  exact (MazurTransfer.order13_field_picard_reflection_norm_certificates).1 K a _

theorem actualReflection_normPiConjugate (a : ReflectionParameter K) (x : NineteenTorsion K) :
    actualReflection K a (actualNineteenTorsionNormHom K schemePiConjugate x) =
      actualNineteenTorsionNormHom K schemePi (actualReflection K a x) := by
  apply (geometricNineteenTorsionDivisorAddEquiv K).injective
  apply Subtype.ext
  have hp (z : NineteenTorsion K) :
      (geometricNineteenTorsionDivisorAddEquiv K (actualNineteenTorsionNormHom K schemePi z)).val =
        pi K (geometricNineteenTorsionDivisorAddEquiv K z).val := by
    rw [normPi_apply, map_add, map_nsmul, map_nsmul,
      geometricNineteenTorsionDivisorAddEquiv_diamond]
    rfl
  have hc (z : NineteenTorsion K) :
      (geometricNineteenTorsionDivisorAddEquiv K (actualNineteenTorsionNormHom K schemePiConjugate z)).val =
        piConjugate K (geometricNineteenTorsionDivisorAddEquiv K z).val := by
    rw [normPiConjugate_apply, map_sub, map_nsmul, map_nsmul,
      geometricNineteenTorsionDivisorAddEquiv_diamond]
    rfl
  have hr (z : NineteenTorsion K) :
      (geometricNineteenTorsionDivisorAddEquiv K (actualReflection K a z)).val =
        reflection K a (geometricNineteenTorsionDivisorAddEquiv K z).val := by
    exact congrArg Subtype.val (actualReflection_class K a z)
  rw [hr, hc, hp, hr]
  exact (MazurTransfer.order13_field_picard_reflection_norm_certificates).2 K a _

end MazurTransfer.ActualNineteenTorsionReflectionNormProofHelpers20261018
theorem solution :
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : ReflectionParameter K) (x : NineteenTorsion K),
      actualReflection K a (actualReflection K a x) = x) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : ReflectionParameter K) (x : NineteenTorsion K),
    actualReflection K a (actualNineteenTorsionNormHom K schemePi x) =
      actualNineteenTorsionNormHom K schemePiConjugate (actualReflection K a x)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : ReflectionParameter K) (x : NineteenTorsion K),
    actualReflection K a (actualNineteenTorsionNormHom K schemePiConjugate x) =
      actualNineteenTorsionNormHom K schemePi (actualReflection K a x)) := by
  exact ⟨MazurTransfer.ActualNineteenTorsionReflectionNormProofHelpers20261018.actualReflection_involution,
    MazurTransfer.ActualNineteenTorsionReflectionNormProofHelpers20261018.actualReflection_normPi,
    MazurTransfer.ActualNineteenTorsionReflectionNormProofHelpers20261018.actualReflection_normPiConjugate⟩
#print axioms solution
