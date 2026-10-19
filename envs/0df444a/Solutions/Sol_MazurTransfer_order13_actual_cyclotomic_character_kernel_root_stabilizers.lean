-- Prove2me | solution 1 for MazurTransfer.order13_actual_cyclotomic_character_kernel_root_stabilizers
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T22:50:34.517491+00:00
-- url     : https://prove2.me/submissions/c6b9c85e-42a9-47a2-88e4-f3115f2687cb

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the explicit cyclotomic reflection and reflected rational
fixed vectors are fixed by every actual arithmetic Galois automorphism
fixing the primitive thirteenth root. Named downstream consumer: the
cyclotomic13 character on the actual quotient kernel.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
import Definitions.Def_MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Theorems.Thm_MazurTransfer_order13_actual_norm_kernel_reflection_galois_certificates
import Theorems.Thm_MazurTransfer_order13_actual_cyclotomic_quotient_reflection_lines
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

local instance sourceRootStabilizerRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients
namespace MazurTransfer.ActualThirteenthRootKernelStabilizerProofHelpers20261018
theorem cyclotomicParameter_fixed {K : Type*} [Field K] [CharZero K]
    (σ : K ≃+* K) (z : K) (hz : IsPrimitiveRoot z 13) (hσ : σ z = z) :
    mapParameter K σ (cyclotomicParameter z hz) = cyclotomicParameter z hz := by
  have ht : σ (cubicPeriod z) = cubicPeriod z := by
    simp only [cubicPeriod, map_add, map_sub, map_pow, map_one, hσ]
  have hs : σ (reflectionS z) = reflectionS z := by
    simp only [reflectionS, quadraticGauss, cubicPeriod, map_add, map_sub, map_pow,
      map_div₀, map_mul, map_ofNat, map_one, hσ]
  dsimp [mapParameter, cyclotomicParameter]
  congr 1

variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
theorem reflected_pi_vector_fixed_of_root_fixed
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z) :
    kernelRepresentation K schemePiConjugate σ (piKernelReflection K (cyclotomicParameter z hz) a) =
      piKernelReflection K (cyclotomicParameter z hz) a := by
  have h := (MazurTransfer.order13_actual_norm_kernel_reflection_galois_certificates).1 K σ (cyclotomicParameter z hz) a
  rw [cyclotomicParameter_fixed σ.toRingEquiv z hz hσ, ha σ] at h
  exact h

theorem reflected_piConjugate_vector_fixed_of_root_fixed
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z) :
    kernelRepresentation K schemePi σ (piConjugateKernelReflection K (cyclotomicParameter z hz) a) =
      piConjugateKernelReflection K (cyclotomicParameter z hz) a := by
  have h := (MazurTransfer.order13_actual_norm_kernel_reflection_galois_certificates).2 K σ (cyclotomicParameter z hz) a
  rw [cyclotomicParameter_fixed σ.toRingEquiv z hz hσ, ha σ] at h
  exact h

theorem pi_character_kernel_fixed_of_root_fixed
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z) (v : Additive (Kernel K schemePiConjugate))
    (hv : v ∈ LinearMap.ker (kernelCharacterLinear K schemePi schemePiConjugate a)) :
    kernelRepresentation K schemePiConjugate σ v = v := by
  rw [(MazurTransfer.order13_actual_cyclotomic_quotient_reflection_lines).1 K (cyclotomicParameter z hz) a ha0] at hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, reflected_pi_vector_fixed_of_root_fixed K z hz a ha σ hσ]

theorem piConjugate_character_kernel_fixed_of_root_fixed
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z) (v : Additive (Kernel K schemePi))
    (hv : v ∈ LinearMap.ker (kernelCharacterLinear K schemePiConjugate schemePi a)) :
    kernelRepresentation K schemePi σ v = v := by
  rw [(MazurTransfer.order13_actual_cyclotomic_quotient_reflection_lines).2 K (cyclotomicParameter z hz) a ha0] at hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, reflected_piConjugate_vector_fixed_of_root_fixed K z hz a ha σ hσ]
end MazurTransfer.ActualThirteenthRootKernelStabilizerProofHelpers20261018
theorem solution :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13)
    (a : Additive (Kernel K schemePi)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z) (v : Additive (Kernel K schemePiConjugate))
    (hv : v ∈ LinearMap.ker (kernelCharacterLinear K schemePi schemePiConjugate a)),
    kernelRepresentation K schemePiConjugate σ v = v) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13)
    (a : Additive (Kernel K schemePiConjugate)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ z = z) (v : Additive (Kernel K schemePi))
    (hv : v ∈ LinearMap.ker (kernelCharacterLinear K schemePiConjugate schemePi a)),
    kernelRepresentation K schemePi σ v = v) := by
  exact ⟨MazurTransfer.ActualThirteenthRootKernelStabilizerProofHelpers20261018.pi_character_kernel_fixed_of_root_fixed,
    MazurTransfer.ActualThirteenthRootKernelStabilizerProofHelpers20261018.piConjugate_character_kernel_fixed_of_root_fixed⟩
#print axioms solution
