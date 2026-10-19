-- Prove2me | solution 1 for MazurTransfer.order13_actual_ordered_good_prime_character_kernel_control
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T01:49:00.127396+00:00
-- url     : https://prove2.me/submissions/ceda4733-d106-4a91-ad17-54bc793c6834

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: choose each actual exact-sequence witness coherently for
its coefficient and continuous H1 maps. The labeled character sequences
are exact at the original norm-kernel H1 globally and on every subgroup.
Named downstream consumer: actual norm-character Kummer kernel control.
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
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterH1ExactSequenceData
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerKernelControlData
import Theorems.Thm_MazurTransfer_order13_actual_ordered_arithmetic_character_sequence_certificates
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricNormPreimages_schemePi_geometricPoint_surjective
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricNormPreimages_schemePiConjugate_geometricPoint_surjective
import Definitions.Def_MazurTransfer_Order13ActualCharacterGoodPrimeKernelLiftsOriginalData20261019
import Theorems.Thm_MazurTransfer_Order13ActualCharacterGoodPrimeKernelLifts_hasGoodPrimeCharacterKummerSequence_of_intertwiners
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

local instance sourceOrderedGoodPrimeCharacterRationalFactProvider20261019 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

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
open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerKernelControl
open RepresentationCharacterTwist ScalarCharacterLine Order13ActualPicardGeometricNormPreimages
open Order13ActualCharacterGoodPrimeKernelLifts
namespace MazurTransfer.ActualOrderedGoodPrimeCharacterKernelControlProofHelpers20261019
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
theorem actual_ordered_good_prime_character_kernel_control
    (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    HasGoodPrimeCharacterKummerSequence K schemePi
      (scalarRepresentation (piConjugateReflectedCharacter K z hz)) (rootsRepresentation K)
      (schemePi_geometricPoint_surjective K) ∧
    HasGoodPrimeCharacterKummerSequence K schemePiConjugate
      (Representation.trivial (ZMod 19) (K ≃ₐ[ℚ] K) (ZMod 19))
      (twist (piConjugateReflectedCharacter K z hz)⁻¹ (rootsRepresentation K))
      (schemePiConjugate_geometricPoint_surjective K) := by
  obtain ⟨hpi, hbar⟩ := (MazurTransfer.order13_actual_ordered_arithmetic_character_sequence_certificates).1 K z hz 𝒱
  obtain ⟨i, p, hi, hp, hk⟩ := hpi
  obtain ⟨j, q, hj, hq, hjk⟩ := hbar
  exact ⟨hasGoodPrimeCharacterKummerSequence_of_intertwiners K schemePi _ _ i p
      (Or.inl rfl) (schemePi_geometricPoint_surjective K) hi hp hk,
    hasGoodPrimeCharacterKummerSequence_of_intertwiners K schemePiConjugate _ _ j q
      (Or.inr rfl) (schemePiConjugate_geometricPoint_surjective K) hj hq hjk⟩

end MazurTransfer.ActualOrderedGoodPrimeCharacterKernelControlProofHelpers20261019
theorem solution : ∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) ,
    HasGoodPrimeCharacterKummerSequence K schemePi
      (scalarRepresentation (piConjugateReflectedCharacter K z hz)) (rootsRepresentation K)
      (schemePi_geometricPoint_surjective K) ∧
    HasGoodPrimeCharacterKummerSequence K schemePiConjugate
      (Representation.trivial (ZMod 19) (K ≃ₐ[ℚ] K) (ZMod 19))
      (twist (piConjugateReflectedCharacter K z hz)⁻¹ (rootsRepresentation K))
      (schemePiConjugate_geometricPoint_surjective K) := by
  exact MazurTransfer.ActualOrderedGoodPrimeCharacterKernelControlProofHelpers20261019.actual_ordered_good_prime_character_kernel_control
#print axioms solution
