-- Prove2me | solution 1 for MazurTransfer.order13_actual_norm_kernel_diamond_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T23:09:54.040997+00:00
-- url     : https://prove2.me/submissions/ef6047c6-987c-41f6-9677-080c0f156e07

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal diamond acts on the actual pi and conjugate
norm kernels by eight and twelve respectively. Named downstream consumer:
the exact order-six arithmetic13 action on the reflected fixed line.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionNormRestrictionOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionDiamondOriginalData20261018
noncomputable section
open scoped CategoryTheory.MonObj
open MazurTransfer CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualNormKernelProductCardinality Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardGeometricDiamondGroupAction Order13ActualPicardSchemeNormGroupHom
open Order13ActualGeometricNineteenTorsionDiamondComparison Order13ActualNineteenTorsionNormPairingAdjoint
attribute [local instance] Order13ActualNormKernelProductCardinality.actualNineteenTorsionProductOriginalGroupProvider20261018
  Order13ActualNormKernelProductCardinality.actualNineteenTorsionProductOriginalCommProvider20261018
  Order13ActualNormKernelProductCardinality.actualNineteenTorsionProductOriginalPiHomProvider20261018
  Order13ActualNormKernelProductCardinality.actualNineteenTorsionProductOriginalConjugateHomProvider20261018
  Order13ActualPicardSchemeNormGroupHom.schemeDiamond_isMonHom
  Order13ActualGeometricNineteenTorsionDiamondComparison.nineteenTorsionDiamondOriginalFactProvider20261018
  Order13ActualGeometricNineteenTorsionDiamondComparison.nineteenTorsionDiamondOriginalAlgebraProvider20261018
namespace MazurTransfer.ActualNormKernelDiamondEigenvalueProofHelpers20261018
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

theorem nineteen_nsmul (x : NineteenTorsion K) : (19 : ℕ) • x = 0 := by
  apply Subtype.ext
  exact x.property

theorem diamond_eq_eight_nsmul_of_normPi_zero (x : NineteenTorsion K)
    (h : actualNineteenTorsionNormHom K schemePi x = 0) :
    actualNineteenTorsionDiamondHom K x = (8 : ℕ) • x := by
  rw [normPi_apply] at h
  apply eq_of_sub_eq_zero
  calc
    actualNineteenTorsionDiamondHom K x - (8 : ℕ) • x =
      (10 : ℕ) • ((3 : ℕ) • x + (2 : ℕ) • actualNineteenTorsionDiamondHom K x) -
        (19 : ℕ) • actualNineteenTorsionDiamondHom K x - (2 : ℕ) • ((19 : ℕ) • x) := by abel
    _ = 0 := by rw [h, nineteen_nsmul, nineteen_nsmul]; simp

theorem diamond_eq_twelve_nsmul_of_normPiConjugate_zero (x : NineteenTorsion K)
    (h : actualNineteenTorsionNormHom K schemePiConjugate x = 0) :
    actualNineteenTorsionDiamondHom K x = (12 : ℕ) • x := by
  rw [normPiConjugate_apply] at h
  apply eq_of_sub_eq_zero
  calc
    actualNineteenTorsionDiamondHom K x - (12 : ℕ) • x =
      -((10 : ℕ) • ((5 : ℕ) • x - (2 : ℕ) • actualNineteenTorsionDiamondHom K x)) -
        (19 : ℕ) • actualNineteenTorsionDiamondHom K x + (2 : ℕ) • ((19 : ℕ) • x) := by abel
    _ = 0 := by rw [h, nineteen_nsmul, nineteen_nsmul]; simp

theorem diamond_pow_apply_of_eigen (n m : ℕ) (x : NineteenTorsion K)
    (h : actualNineteenTorsionDiamondHom K x = m • x) :
    ((actualNineteenTorsionDiamondHom K : NineteenTorsion K → NineteenTorsion K)^[n]) x = m ^ n • x := by
  induction n with
  | zero => simpa using (one_nsmul x).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [ih, map_nsmul, h, smul_smul, pow_succ]
end MazurTransfer.ActualNormKernelDiamondEigenvalueProofHelpers20261018
theorem solution :
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : NineteenTorsion K)
    (h : actualNineteenTorsionNormHom K schemePi x = 0),
    actualNineteenTorsionDiamondHom K x = (8 : ℕ) • x) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : NineteenTorsion K)
    (h : actualNineteenTorsionNormHom K schemePiConjugate x = 0),
    actualNineteenTorsionDiamondHom K x = (12 : ℕ) • x) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (n m : ℕ) (x : NineteenTorsion K)
    (h : actualNineteenTorsionDiamondHom K x = m • x),
    ((actualNineteenTorsionDiamondHom K : NineteenTorsion K → NineteenTorsion K)^[n]) x = m ^ n • x) := by
  exact ⟨MazurTransfer.ActualNormKernelDiamondEigenvalueProofHelpers20261018.diamond_eq_eight_nsmul_of_normPi_zero,
    MazurTransfer.ActualNormKernelDiamondEigenvalueProofHelpers20261018.diamond_eq_twelve_nsmul_of_normPiConjugate_zero,
    MazurTransfer.ActualNormKernelDiamondEigenvalueProofHelpers20261018.diamond_pow_apply_of_eigen⟩
#print axioms solution
