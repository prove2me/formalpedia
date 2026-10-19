-- Prove2me | solution 1 for MazurTransfer.order13_actual_reflected_line_generator_scalars
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T23:23:12.229435+00:00
-- url     : https://prove2.me/submissions/e4fe50d8-45c1-40d3-add0-8153dd360438

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual arithmetic generator z ↦ z² acts on reflected
fixed vectors by twelve or eight in F19. Named downstream consumer:
the exact order-six thirteenth-cyclotomic kernel characters.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
import Definitions.Def_MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Theorems.Thm_MazurTransfer_order13_actual_norm_kernel_reflection_galois_certificates
import Theorems.Thm_MazurTransfer_Order13CyclotomicReflectionGeneratorOrbit_mapParameter_generator
import Theorems.Thm_MazurTransfer_Order13ActualReflectionDiamondOrbitAction_actualReflection_fifth
import Theorems.Thm_MazurTransfer_order13_actual_norm_kernel_diamond_eigenvalues
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelCyclotomicQuotient
open Order13ActualNormKernelF19Representation NineteenRootsGaloisRepresentation
open Order13ActualNineteenTorsionNormPairingAdjoint Order13ActualNormKernelProductCardinality
open Order13ActualNormKernelNineteenEmbedding
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018 kernelNineteenEmbeddingOriginalFiniteProvider20261018

open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualNormKernelRanksTwo
open Order13ActualPicardSchemeNineteenNorm
attribute [local instance] originalNormKernelRanksTwoPiFiniteProvider20261018 originalNormKernelRanksTwoConjugateFiniteProvider20261018 originalNormKernelRanksTwoPiExponentProvider20261018 originalNormKernelRanksTwoConjugateExponentProvider20261018 originalNormKernelRanksTwoPiModuleProvider20261018 originalNormKernelRanksTwoConjugateModuleProvider20261018

local instance sourceReflectedGeneratorRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients
open Order13ActualNineteenTorsionReflection Order13ActualGeometricNineteenTorsionDiamondComparison
open Order13ReflectionParameterArithmetic
namespace MazurTransfer.ActualReflectedLineGeneratorScalarProofHelpers20261018
def fifthParameter {K : Type*} [Field K] (r : ReflectionParameter K) : ReflectionParameter K :=
  diamondParameter (diamondParameter (diamondParameter (diamondParameter (diamondParameter r))))
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
theorem piKernelReflection_fifth (r : ReflectionParameter K) (a : Additive (Kernel K schemePi)) :
    piKernelReflection K (fifthParameter r) a = (8 ^ 5 : ℕ) • piKernelReflection K r a := by
  dsimp only [fifthParameter]
  apply kernelNineteenAddHom_injective K schemePiConjugate
  rw [piKernelReflection_embed, map_nsmul, piKernelReflection_embed, Order13ActualReflectionDiamondOrbitAction.actualReflection_fifth,
    (MazurTransfer.order13_actual_norm_kernel_diamond_eigenvalues).2.2 K 5 8 _ ((MazurTransfer.order13_actual_norm_kernel_diamond_eigenvalues).1 K _
      (kernelNineteenAddHom_norm_zero K schemePi a)), map_nsmul]

theorem piConjugateKernelReflection_fifth (r : ReflectionParameter K)
    (a : Additive (Kernel K schemePiConjugate)) :
    piConjugateKernelReflection K (fifthParameter r) a = (12 ^ 5 : ℕ) • piConjugateKernelReflection K r a := by
  dsimp only [fifthParameter]
  apply kernelNineteenAddHom_injective K schemePi
  rw [piConjugateKernelReflection_embed, map_nsmul, piConjugateKernelReflection_embed, Order13ActualReflectionDiamondOrbitAction.actualReflection_fifth,
    (MazurTransfer.order13_actual_norm_kernel_diamond_eigenvalues).2.2 K 5 12 _ ((MazurTransfer.order13_actual_norm_kernel_diamond_eigenvalues).2.1 K _
      (kernelNineteenAddHom_norm_zero K schemePiConjugate a)), map_nsmul]

theorem reflected_pi_vector_generator_scalar
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z ^ 2) :
    kernelRepresentation K schemePiConjugate σ (piKernelReflection K (cyclotomicParameter z hz) a) =
      (12 : ZMod 19) • piKernelReflection K (cyclotomicParameter z hz) a := by
  rw [(MazurTransfer.order13_actual_norm_kernel_reflection_galois_certificates).1 K σ (cyclotomicParameter z hz) a, Order13CyclotomicReflectionGeneratorOrbit.mapParameter_generator σ.toRingEquiv hz hσ, ha σ]
  have hf := piKernelReflection_fifth K (cyclotomicParameter z hz) a
  dsimp only [fifthParameter] at hf
  rw [hf]
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod 19)]
  rw [show ((8 ^ 5 : ℕ) : ZMod 19) = 12 by decide]

theorem reflected_piConjugate_vector_generator_scalar
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z ^ 2) :
    kernelRepresentation K schemePi σ (piConjugateKernelReflection K (cyclotomicParameter z hz) a) =
      (8 : ZMod 19) • piConjugateKernelReflection K (cyclotomicParameter z hz) a := by
  rw [(MazurTransfer.order13_actual_norm_kernel_reflection_galois_certificates).2 K σ (cyclotomicParameter z hz) a, Order13CyclotomicReflectionGeneratorOrbit.mapParameter_generator σ.toRingEquiv hz hσ, ha σ]
  have hf := piConjugateKernelReflection_fifth K (cyclotomicParameter z hz) a
  dsimp only [fifthParameter] at hf
  rw [hf]
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod 19)]
  rw [show ((12 ^ 5 : ℕ) : ZMod 19) = 8 by decide]

end MazurTransfer.ActualReflectedLineGeneratorScalarProofHelpers20261018
theorem solution :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z ^ 2) ,
    kernelRepresentation K schemePiConjugate σ (piKernelReflection K (cyclotomicParameter z hz) a) =
      (12 : ZMod 19) • piKernelReflection K (cyclotomicParameter z hz) a) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z ^ 2) ,
    kernelRepresentation K schemePi σ (piConjugateKernelReflection K (cyclotomicParameter z hz) a) =
      (8 : ZMod 19) • piConjugateKernelReflection K (cyclotomicParameter z hz) a) := by
  exact ⟨MazurTransfer.ActualReflectedLineGeneratorScalarProofHelpers20261018.reflected_pi_vector_generator_scalar,
    MazurTransfer.ActualReflectedLineGeneratorScalarProofHelpers20261018.reflected_piConjugate_vector_generator_scalar⟩
#print axioms solution
