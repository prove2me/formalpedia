-- Prove2me | solution 1 for MazurTransfer.order13_actual_ordered_arithmetic_character_sequence_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T00:54:59.650452+00:00
-- url     : https://prove2.me/submissions/b0c2d806-4609-40c2-9e8a-6f4ca836c0bf

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: order the two actual arithmetic character exact sequences
using the PREVIOUSLY CHECKED rational infinity-class norm-kernel identification
and its actual fixed-point descent. The infinity cyclic nineteen lies in the
conjugate norm kernel and the rational pi kernel is trivial.
Named downstream consumer: the labeled exceptional-prime local Kummer and
norm Selmer conditions. No representation splitting is asserted.
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
import Definitions.Def_MazurTransfer_Order13ActualComplementaryCharacterExactSequenceOriginalFixedVectorAndPredicateData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelEigenCharacterIntertwiningOriginalDataAndEquivarianceCertificate20261018
import Theorems.Thm_MazurTransfer_order13_actual_complementary_character_exact_sequence_certificates
import Theorems.Thm_MazurTransfer_thirteenth_character_kernels_ranges_and_actual_image_cardinalities
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelInvariantDimensions_actual_kernel_invariant_finranks
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

local instance sourceOrderedCharacterSequencesRationalFactProvider20261019 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients
open Order13ActualNineteenTorsionReflection Order13ActualGeometricNineteenTorsionDiamondComparison
open MazurTransfer.ThirteenToNineteenCharacters MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018
open MazurTransfer.Order13ActualArithmeticCharacterExactSequence MazurTransfer.ScalarCharacterLine
open Order13ActualComplementaryCharacterExactSequence Order13ActualNormKernelEigenCharacterQuotient RepresentationCharacterTwist
open Order13ActualNormKernelCrossPairing
open Order13ActualNormKernelInvariantDimensions
namespace MazurTransfer.ActualOrderedCharacterSequenceProofHelpers20261019
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
theorem actual_ordered_character_sequences
    (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    HasArithmeticCharacterExactSequence K schemePi (piConjugateReflectedCharacter K z hz) ∧
      HasComplementaryCharacterExactSequence K schemePiConjugate (piConjugateReflectedCharacter K z hz) := by
  have hd := actual_kernel_invariant_finranks K 𝒱
  rcases (MazurTransfer.order13_actual_complementary_character_exact_sequence_certificates).2.2 K z hz 𝒱 with
    ⟨hp, _, _, _⟩ | ⟨_, hb, hp, _⟩
  · rw [hd.1] at hp
    exact False.elim (Nat.zero_ne_one hp)
  · exact ⟨hp, hb⟩

theorem actual_ordered_character_sequences_with_image
    (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    HasArithmeticCharacterExactSequence K schemePi (piConjugateReflectedCharacter K z hz) ∧
      HasComplementaryCharacterExactSequence K schemePiConjugate (piConjugateReflectedCharacter K z hz) ∧
      Nat.card (piConjugateReflectedCharacter K z hz).range = 6 := by
  have h := actual_ordered_character_sequences K z hz 𝒱
  exact ⟨h.1, h.2, (MazurTransfer.thirteenth_character_kernels_ranges_and_actual_image_cardinalities).2.2.2.2.2.2.2.2.2 K z hz⟩

end MazurTransfer.ActualOrderedCharacterSequenceProofHelpers20261019
theorem solution :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) ,
    HasArithmeticCharacterExactSequence K schemePi (piConjugateReflectedCharacter K z hz) ∧
      HasComplementaryCharacterExactSequence K schemePiConjugate (piConjugateReflectedCharacter K z hz)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) ,
    HasArithmeticCharacterExactSequence K schemePi (piConjugateReflectedCharacter K z hz) ∧
      HasComplementaryCharacterExactSequence K schemePiConjugate (piConjugateReflectedCharacter K z hz) ∧
      Nat.card (piConjugateReflectedCharacter K z hz).range = 6) := by
  exact ⟨MazurTransfer.ActualOrderedCharacterSequenceProofHelpers20261019.actual_ordered_character_sequences, MazurTransfer.ActualOrderedCharacterSequenceProofHelpers20261019.actual_ordered_character_sequences_with_image⟩
#print axioms solution
