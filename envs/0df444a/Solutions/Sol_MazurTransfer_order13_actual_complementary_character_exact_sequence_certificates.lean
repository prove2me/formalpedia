-- Prove2me | solution 1 for MazurTransfer.order13_actual_complementary_character_exact_sequence_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T00:38:21.946136+00:00
-- url     : https://prove2.me/submissions/c56c8863-1bd1-469d-9f77-c8f7ac7e494f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME actual norm factor containing the rational fixed
line is an extension of literal mu19 twisted by chi13 inverse by the trivial
representation. Together with the opposite norm factor's checked sequence,
this identifies both actual arithmetic character exact sequences.
Named downstream consumer: exceptional-prime local Kummer and norm Selmer bounds.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
import Definitions.Def_MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Definitions.Def_MazurTransfer_Order13ActualThirteenthCyclotomicReflectedCharacterOriginalData20261018
import Definitions.Def_MazurTransfer_Order13ActualArithmeticCharacterExactSequenceOriginalPredicateDataExplicitFiniteModuleNamespaceV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterIntertwiningOriginalData20261018
import Theorems.Thm_MazurTransfer_order13_actual_thirteenth_cyclotomic_kernel_character_certificates
import Theorems.Thm_MazurTransfer_order13_actual_cyclotomic_quotient_reflection_lines
import Theorems.Thm_MazurTransfer_scalar_character_line_injectivity_and_range
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicCharacter_kernelCharacterLinear_surjective_of_cross
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCrossPairing_pi_cross_left_nondegenerate
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCrossPairing_piConjugate_cross_left_nondegenerate
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelInvariantDimensions_actual_kernel_invariant_finranks
import Definitions.Def_MazurTransfer_Order13ActualComplementaryCharacterExactSequenceOriginalFixedVectorAndPredicateData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelEigenCharacterIntertwiningOriginalDataAndEquivarianceCertificate20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelEigenCharacterQuotient_kernelEigenCharacterIntertwining_surjective
import Theorems.Thm_MazurTransfer_order13_actual_complementary_character_kernel_certificates
import Theorems.Thm_MazurTransfer_order13_actual_arithmetic_character_exact_sequence_certificates
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

local instance sourceComplementaryCharacterSequencesRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients
open Order13ActualNineteenTorsionReflection Order13ActualGeometricNineteenTorsionDiamondComparison
open MazurTransfer.ThirteenToNineteenCharacters MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018
open MazurTransfer.Order13ActualArithmeticCharacterExactSequence MazurTransfer.ScalarCharacterLine
open Order13ActualComplementaryCharacterExactSequence Order13ActualNormKernelEigenCharacterQuotient RepresentationCharacterTwist
open Order13ActualNormKernelCrossPairing
namespace MazurTransfer.ActualComplementaryCharacterExactSequenceProofHelpers20261018
theorem actual_invariant_dimension_dichotomy (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 1 ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 0) ∨
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 0 ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 1) := by
  have h := Order13ActualNormKernelInvariantDimensions.actual_kernel_invariant_finranks K 𝒱
  exact Or.inr ⟨h.1, h.2⟩
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
theorem pi_fixed_line_complementary_character_exact_sequence
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a) :
    HasComplementaryCharacterExactSequence K schemePi (piReflectedCharacter K z hz) := by
  let b := piKernelReflection K (cyclotomicParameter z hz) a
  have hb : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ b =
      (piReflectedCharacter K z hz σ : ZMod 19) • b := (MazurTransfer.order13_actual_thirteenth_cyclotomic_kernel_character_certificates).1 K z hz a ha
  have hb0 : b ≠ 0 := by
    intro h
    apply ha0
    apply (piKernelReflection K (cyclotomicParameter z hz)).injective
    exact h.trans (map_zero (piKernelReflection K (cyclotomicParameter z hz))).symm
  let i := fixedVectorIntertwining K schemePi a ha
  let p := kernelEigenCharacterIntertwining K schemePiConjugate schemePi (piReflectedCharacter K z hz) b hb
  refine ⟨i, p, LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton (ZMod 19) ha0),
    kernelEigenCharacterIntertwining_surjective K schemePiConjugate schemePi
      (piConjugate_cross_left_nondegenerate K) _ b hb0 hb, ?_⟩
  exact (LinearMap.range_toSpanSingleton a).trans
    ((MazurTransfer.order13_actual_complementary_character_kernel_certificates).1 K (cyclotomicParameter z hz) a ha0).symm

theorem piConjugate_fixed_line_complementary_character_exact_sequence
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a) :
    HasComplementaryCharacterExactSequence K schemePiConjugate (piConjugateReflectedCharacter K z hz) := by
  let b := piConjugateKernelReflection K (cyclotomicParameter z hz) a
  have hb : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ b =
      (piConjugateReflectedCharacter K z hz σ : ZMod 19) • b := (MazurTransfer.order13_actual_thirteenth_cyclotomic_kernel_character_certificates).2.1 K z hz a ha
  have hb0 : b ≠ 0 := by
    intro h
    apply ha0
    apply (piConjugateKernelReflection K (cyclotomicParameter z hz)).injective
    exact h.trans (map_zero (piConjugateKernelReflection K (cyclotomicParameter z hz))).symm
  let i := fixedVectorIntertwining K schemePiConjugate a ha
  let p := kernelEigenCharacterIntertwining K schemePi schemePiConjugate (piConjugateReflectedCharacter K z hz) b hb
  refine ⟨i, p, LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton (ZMod 19) ha0),
    kernelEigenCharacterIntertwining_surjective K schemePi schemePiConjugate
      (pi_cross_left_nondegenerate K) _ b hb0 hb, ?_⟩
  exact (LinearMap.range_toSpanSingleton a).trans
    ((MazurTransfer.order13_actual_complementary_character_kernel_certificates).2 K (cyclotomicParameter z hz) a ha0).symm

theorem actual_pair_of_arithmetic_character_sequences
    (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 1 ∧
      HasComplementaryCharacterExactSequence K schemePi (piReflectedCharacter K z hz) ∧
      HasArithmeticCharacterExactSequence K schemePiConjugate (piReflectedCharacter K z hz) ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 0) ∨
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 1 ∧
      HasComplementaryCharacterExactSequence K schemePiConjugate (piConjugateReflectedCharacter K z hz) ∧
      HasArithmeticCharacterExactSequence K schemePi (piConjugateReflectedCharacter K z hz) ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 0) := by
  rcases actual_invariant_dimension_dichotomy K 𝒱 with ⟨hp, hb⟩ | ⟨hp, hb⟩
  · have hpos : 0 < Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants := by rw [hp]; decide
    obtain ⟨a, ha⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have ha0 : a.val ≠ 0 := fun h => ha (Subtype.ext h)
    exact Or.inl ⟨hp, pi_fixed_line_complementary_character_exact_sequence K z hz a.val ha0 (fun σ => a.property σ),
      (MazurTransfer.order13_actual_arithmetic_character_exact_sequence_certificates).1 K z hz a.val ha0 (fun σ => a.property σ), hb⟩
  · have hpos : 0 < Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants := by rw [hb]; decide
    obtain ⟨a, ha⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have ha0 : a.val ≠ 0 := fun h => ha (Subtype.ext h)
    exact Or.inr ⟨hb, piConjugate_fixed_line_complementary_character_exact_sequence K z hz a.val ha0 (fun σ => a.property σ),
      (MazurTransfer.order13_actual_arithmetic_character_exact_sequence_certificates).2.1 K z hz a.val ha0 (fun σ => a.property σ), hp⟩

end MazurTransfer.ActualComplementaryCharacterExactSequenceProofHelpers20261018
theorem solution :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePi)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePi σ a = a) ,
    HasComplementaryCharacterExactSequence K schemePi (piReflectedCharacter K z hz)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (a : Additive (Kernel K schemePiConjugate)) (ha0 : a ≠ 0)
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K schemePiConjugate σ a = a) ,
    HasComplementaryCharacterExactSequence K schemePiConjugate (piConjugateReflectedCharacter K z hz)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) ,
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 1 ∧
      HasComplementaryCharacterExactSequence K schemePi (piReflectedCharacter K z hz) ∧
      HasArithmeticCharacterExactSequence K schemePiConjugate (piReflectedCharacter K z hz) ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 0) ∨
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 1 ∧
      HasComplementaryCharacterExactSequence K schemePiConjugate (piConjugateReflectedCharacter K z hz) ∧
      HasArithmeticCharacterExactSequence K schemePi (piConjugateReflectedCharacter K z hz) ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 0)) := by
  exact ⟨MazurTransfer.ActualComplementaryCharacterExactSequenceProofHelpers20261018.pi_fixed_line_complementary_character_exact_sequence, MazurTransfer.ActualComplementaryCharacterExactSequenceProofHelpers20261018.piConjugate_fixed_line_complementary_character_exact_sequence, MazurTransfer.ActualComplementaryCharacterExactSequenceProofHelpers20261018.actual_pair_of_arithmetic_character_sequences⟩
#print axioms solution
