-- Prove2me | solution 1 for MazurTransfer.order13_actual_norm_kernel_reflection_galois_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T22:30:24.950916+00:00
-- url     : https://prove2.me/submissions/36afefd6-3c9b-4b43-bf47-c059622b46d1

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: reflection exchanges the COMPLETE kernels of the SAME
actual Picard norm maps, with their intrinsic nineteen-torsion embeddings
and the EXISTING arithmetic Galois action. Named downstream consumer: the
reflection-generated line in the actual cyclotomic quotient kernel.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
import Theorems.Thm_MazurTransfer_Order13ActualReflectionArithmeticGaloisCovariance_actualReflection_galois
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelNineteenEmbedding_kernelNineteenAddHom_galois
noncomputable section
open MazurTransfer CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open GoodReductionJacobian NeronModelInfra
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualNormKernelProductCardinality
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormKernelNineteenEmbedding
open Order13ReflectionParameter Order13ActualNineteenTorsionReflection
open Order13ActualNineteenTorsionNormPairingAdjoint
open scoped CategoryTheory.MonObj
attribute [local instance] Order13ActualNineteenTorsionReflection.actualReflectionOriginalGroupProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalCommProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalPiHomProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalConjugateHomProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalFactProvider20261018
  Order13ActualNineteenTorsionReflection.actualReflectionOriginalAlgebraProvider20261018
attribute [local instance] MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiFiniteProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoConjugateFiniteProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiExponentProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoConjugateExponentProvider20261018
open Order13ActualNormKernelReflection Order13ActualReflectionArithmeticGaloisCovariance
open Order13ActualReflectionCoefficientCovariance Order13ActualNormKernelF19Representation
attribute [local instance] MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPrimeProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiKernelFiniteProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoConjugateKernelFiniteProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoPiModuleProvider20261018
  MazurTransfer.Order13ActualNormKernelRanksTwo.originalNormKernelRanksTwoConjugateModuleProvider20261018
namespace MazurTransfer.ActualNormKernelReflectionGaloisProofHelpers20261018
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
theorem piKernelReflection_galois (σ : K ≃ₐ[ℚ] K) (a : ReflectionParameter K)
    (z : Additive (Kernel K schemePi)) :
    kernelRepresentation K schemePiConjugate σ (piKernelReflection K a z) =
      piKernelReflection K (mapParameter K σ.toRingEquiv a) (kernelRepresentation K schemePi σ z) := by
  apply kernelNineteenAddHom_injective K schemePiConjugate
  rw [← kernelNineteenAddHom_galois, piKernelReflection_embed, actualReflection_galois,
    kernelNineteenAddHom_galois, piKernelReflection_embed]

theorem piConjugateKernelReflection_galois (σ : K ≃ₐ[ℚ] K) (a : ReflectionParameter K)
    (z : Additive (Kernel K schemePiConjugate)) :
    kernelRepresentation K schemePi σ (piConjugateKernelReflection K a z) =
      piConjugateKernelReflection K (mapParameter K σ.toRingEquiv a)
        (kernelRepresentation K schemePiConjugate σ z) := by
  apply kernelNineteenAddHom_injective K schemePi
  rw [← kernelNineteenAddHom_galois, piConjugateKernelReflection_embed, actualReflection_galois,
    kernelNineteenAddHom_galois, piConjugateKernelReflection_embed]
end MazurTransfer.ActualNormKernelReflectionGaloisProofHelpers20261018
theorem solution :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (a : ReflectionParameter K)
    (z : Additive (Kernel K schemePi)),
    kernelRepresentation K schemePiConjugate σ (piKernelReflection K a z) =
      piKernelReflection K (mapParameter K σ.toRingEquiv a) (kernelRepresentation K schemePi σ z)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (a : ReflectionParameter K)
    (z : Additive (Kernel K schemePiConjugate)),
    kernelRepresentation K schemePi σ (piConjugateKernelReflection K a z) =
      piConjugateKernelReflection K (mapParameter K σ.toRingEquiv a) (kernelRepresentation K schemePiConjugate σ z)) := by
  exact ⟨MazurTransfer.ActualNormKernelReflectionGaloisProofHelpers20261018.piKernelReflection_galois,
    MazurTransfer.ActualNormKernelReflectionGaloisProofHelpers20261018.piConjugateKernelReflection_galois⟩
#print axioms solution
