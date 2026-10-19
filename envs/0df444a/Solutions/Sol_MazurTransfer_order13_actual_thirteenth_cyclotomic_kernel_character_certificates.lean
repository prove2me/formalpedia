-- Prove2me | solution 1 for MazurTransfer.order13_actual_thirteenth_cyclotomic_kernel_character_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T23:38:23.348707+00:00
-- url     : https://prove2.me/submissions/fd484204-93c8-4978-ac35-e823528bc44f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME actual cyclotomic quotient kernel has an explicit
arithmetic13 character of exact order six, with both factor orderings kept.
The Galois power map is for the literal primitive thirteenth root.
Named downstream consumer: complete norm representation exact sequences
and the exceptional-prime local Kummer and Selmer arguments.
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
import Definitions.Def_MazurTransfer_Order13ActualThirteenthCyclotomicReflectedCharacterOriginalData20261018
import Theorems.Thm_MazurTransfer_order13_actual_reflected_line_generator_scalars
import Theorems.Thm_MazurTransfer_cyclic_quotient_action_eq_character_smul
import Theorems.Thm_MazurTransfer_thirteen_to_nineteen_character_certificates
import Theorems.Thm_MazurTransfer_thirteenth_root_galois_quotient_certificates
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

local instance sourceThirteenthCharacterRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients
open Order13ActualNineteenTorsionReflection Order13ActualGeometricNineteenTorsionDiamondComparison
open MazurTransfer.ThirteenToNineteenCharacters MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018
namespace MazurTransfer.ActualCyclotomicThirteenKernelCharacterProofHelpers20261018
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

theorem pi_reflected_vector_character
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a) (σ : K ≃ₐ[ℚ] K) :
    kernelRepresentation K schemePiConjugate σ (piKernelReflection K (cyclotomicParameter z hz) a) =
      (piReflectedCharacter K z hz σ : ZMod 19) • piKernelReflection K (cyclotomicParameter z hz) a := by
  obtain ⟨g, hgz, hgq⟩ := (MazurTransfer.thirteenth_root_galois_quotient_certificates).2.2.2.2 K z hz
  refine MazurTransfer.cyclic_quotient_action_eq_character_smul (kernelRepresentation K schemePiConjugate) (hz.autToPow ℚ)
    character generator ?_ g hgq (piKernelReflection K (cyclotomicParameter z hz) a) ?_ ?_ σ
  · intro y
    obtain ⟨n, hn⟩ := (MazurTransfer.thirteen_to_nineteen_character_certificates).2.2.2.1 y
    exact ⟨n.val, hn⟩
  · intro s hs
    exact reflected_pi_vector_fixed_of_root_fixed K z hz a ha s ((MazurTransfer.thirteenth_root_galois_quotient_certificates).2.2.2.1 K z hz s hs)
  · rw [(MazurTransfer.thirteen_to_nineteen_character_certificates).1]
    exact (MazurTransfer.order13_actual_reflected_line_generator_scalars).1 K z hz a ha g hgz

theorem piConjugate_reflected_vector_character
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a) (σ : K ≃ₐ[ℚ] K) :
    kernelRepresentation K schemePi σ (piConjugateKernelReflection K (cyclotomicParameter z hz) a) =
      (piConjugateReflectedCharacter K z hz σ : ZMod 19) • piConjugateKernelReflection K (cyclotomicParameter z hz) a := by
  obtain ⟨g, hgz, hgq⟩ := (MazurTransfer.thirteenth_root_galois_quotient_certificates).2.2.2.2 K z hz
  refine MazurTransfer.cyclic_quotient_action_eq_character_smul (kernelRepresentation K schemePi) (hz.autToPow ℚ)
    conjugateCharacter generator ?_ g hgq (piConjugateKernelReflection K (cyclotomicParameter z hz) a) ?_ ?_ σ
  · intro y
    obtain ⟨n, hn⟩ := (MazurTransfer.thirteen_to_nineteen_character_certificates).2.2.2.1 y
    exact ⟨n.val, hn⟩
  · intro s hs
    exact reflected_piConjugate_vector_fixed_of_root_fixed K z hz a ha s ((MazurTransfer.thirteenth_root_galois_quotient_certificates).2.2.2.1 K z hz s hs)
  · rw [(MazurTransfer.thirteen_to_nineteen_character_certificates).2.2.1]
    exact (MazurTransfer.order13_actual_reflected_line_generator_scalars).2 K z hz a ha g hgz

theorem pi_character_on_actual_quotient_kernel
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a)
    (σ : K ≃ₐ[ℚ] K) (v : Additive (Kernel K schemePiConjugate))
    (hv : v ∈ LinearMap.ker (kernelCharacterLinear K schemePi schemePiConjugate a)) :
    kernelRepresentation K schemePiConjugate σ v = (piReflectedCharacter K z hz σ : ZMod 19) • v := by
  rw [(MazurTransfer.order13_actual_cyclotomic_quotient_reflection_lines).1 K (cyclotomicParameter z hz) a ha0] at hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, pi_reflected_vector_character K z hz a ha σ, smul_comm]

theorem piConjugate_character_on_actual_quotient_kernel
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a)
    (σ : K ≃ₐ[ℚ] K) (v : Additive (Kernel K schemePi))
    (hv : v ∈ LinearMap.ker (kernelCharacterLinear K schemePiConjugate schemePi a)) :
    kernelRepresentation K schemePi σ v = (piConjugateReflectedCharacter K z hz σ : ZMod 19) • v := by
  rw [(MazurTransfer.order13_actual_cyclotomic_quotient_reflection_lines).2 K (cyclotomicParameter z hz) a ha0] at hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, piConjugate_reflected_vector_character K z hz a ha σ, smul_comm]

theorem piReflectedCharacter_exact_order_six (z : K) (hz : IsPrimitiveRoot z 13) :
    (∀ σ : K ≃ₐ[ℚ] K, piReflectedCharacter K z hz σ ^ 6 = 1) ∧
      ∃ σ : K ≃ₐ[ℚ] K, orderOf (piReflectedCharacter K z hz σ) = 6 := by
  constructor
  · intro σ
    obtain ⟨n, hn⟩ := (MazurTransfer.thirteen_to_nineteen_character_certificates).2.2.2.1 (hz.autToPow ℚ σ)
    change character (hz.autToPow ℚ σ) ^ 6 = 1
    have hc : character generator ^ 6 = 1 := by
      rw [← (MazurTransfer.thirteen_to_nineteen_character_certificates).2.2.2.2.1]
      exact pow_orderOf_eq_one _
    rw [hn, map_pow, ← pow_mul, Nat.mul_comm, pow_mul, hc, one_pow]
  · obtain ⟨g, _, hg⟩ := (MazurTransfer.thirteenth_root_galois_quotient_certificates).2.2.2.2 K z hz
    refine ⟨g, ?_⟩
    change orderOf (character (hz.autToPow ℚ g)) = 6
    rw [hg, (MazurTransfer.thirteen_to_nineteen_character_certificates).2.2.2.2.1]

theorem piConjugateReflectedCharacter_exact_order_six (z : K) (hz : IsPrimitiveRoot z 13) :
    (∀ σ : K ≃ₐ[ℚ] K, piConjugateReflectedCharacter K z hz σ ^ 6 = 1) ∧
      ∃ σ : K ≃ₐ[ℚ] K, orderOf (piConjugateReflectedCharacter K z hz σ) = 6 := by
  constructor
  · intro σ
    obtain ⟨n, hn⟩ := (MazurTransfer.thirteen_to_nineteen_character_certificates).2.2.2.1 (hz.autToPow ℚ σ)
    change conjugateCharacter (hz.autToPow ℚ σ) ^ 6 = 1
    have hc : conjugateCharacter generator ^ 6 = 1 := by
      rw [← (MazurTransfer.thirteen_to_nineteen_character_certificates).2.2.2.2.2]
      exact pow_orderOf_eq_one _
    rw [hn, map_pow, ← pow_mul, Nat.mul_comm, pow_mul, hc, one_pow]
  · obtain ⟨g, _, hg⟩ := (MazurTransfer.thirteenth_root_galois_quotient_certificates).2.2.2.2 K z hz
    refine ⟨g, ?_⟩
    change orderOf (conjugateCharacter (hz.autToPow ℚ g)) = 6
    rw [hg, (MazurTransfer.thirteen_to_nineteen_character_certificates).2.2.2.2.2]

end MazurTransfer.ActualCyclotomicThirteenKernelCharacterProofHelpers20261018
theorem solution :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a) (σ : K ≃ₐ[ℚ] K) ,
    kernelRepresentation K schemePiConjugate σ (piKernelReflection K (cyclotomicParameter z hz) a) =
      (piReflectedCharacter K z hz σ : ZMod 19) • piKernelReflection K (cyclotomicParameter z hz) a) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a) (σ : K ≃ₐ[ℚ] K) ,
    kernelRepresentation K schemePi σ (piConjugateKernelReflection K (cyclotomicParameter z hz) a) =
      (piConjugateReflectedCharacter K z hz σ : ZMod 19) • piConjugateKernelReflection K (cyclotomicParameter z hz) a) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a)
    (σ : K ≃ₐ[ℚ] K) (v : Additive (Kernel K schemePiConjugate))
    (hv : v ∈ LinearMap.ker (kernelCharacterLinear K schemePi schemePiConjugate a)) ,
    kernelRepresentation K schemePiConjugate σ v = (piReflectedCharacter K z hz σ : ZMod 19) • v) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a)
    (σ : K ≃ₐ[ℚ] K) (v : Additive (Kernel K schemePi))
    (hv : v ∈ LinearMap.ker (kernelCharacterLinear K schemePiConjugate schemePi a)) ,
    kernelRepresentation K schemePi σ v = (piConjugateReflectedCharacter K z hz σ : ZMod 19) • v) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) ,
    (∀ σ : K ≃ₐ[ℚ] K, piReflectedCharacter K z hz σ ^ 6 = 1) ∧
      ∃ σ : K ≃ₐ[ℚ] K, orderOf (piReflectedCharacter K z hz σ) = 6) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) ,
    (∀ σ : K ≃ₐ[ℚ] K, piConjugateReflectedCharacter K z hz σ ^ 6 = 1) ∧
      ∃ σ : K ≃ₐ[ℚ] K, orderOf (piConjugateReflectedCharacter K z hz σ) = 6) := by
  exact ⟨MazurTransfer.ActualCyclotomicThirteenKernelCharacterProofHelpers20261018.pi_reflected_vector_character, MazurTransfer.ActualCyclotomicThirteenKernelCharacterProofHelpers20261018.piConjugate_reflected_vector_character, MazurTransfer.ActualCyclotomicThirteenKernelCharacterProofHelpers20261018.pi_character_on_actual_quotient_kernel, MazurTransfer.ActualCyclotomicThirteenKernelCharacterProofHelpers20261018.piConjugate_character_on_actual_quotient_kernel, MazurTransfer.ActualCyclotomicThirteenKernelCharacterProofHelpers20261018.piReflectedCharacter_exact_order_six, MazurTransfer.ActualCyclotomicThirteenKernelCharacterProofHelpers20261018.piConjugateReflectedCharacter_exact_order_six⟩
#print axioms solution
