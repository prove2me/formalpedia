-- Prove2me | solution 1 for MazurTransfer.order13_actual_selected_character_coherent_inclusion_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T03:13:30.476321+00:00
-- url     : https://prove2.me/submissions/2f8324a8-99d1-47bf-84d2-6190c64fa21f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: keep BOTH previously selected actual character quotient
intertwiners and construct character inclusions with ranges EXACTLY their
kernels. No independently selected quotient replaces either original map.
Named downstream consumer: actual continuous-H1 character kernel control
for the norm Kummer maps and their numerical norm quotient estimates.
-/
import Definitions.Def_MazurTransfer_Order13ActualOrderedCharacterContinuousH1OriginalChosenQuotientsAndKummerDataFixedKernelActionsAndContinuousNamespacesV320261019
import Theorems.Thm_MazurTransfer_OneDimensionalSelectedQuotientKernel_exists_injective_with_selected_kernel
import Theorems.Thm_MazurTransfer_order13_actual_ordered_arithmetic_character_sequence_certificates
import Definitions.Def_MazurTransfer_Order13ActualSelectedCharacterOriginalCoherentInclusionData20261019
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
attribute [local instance] sourceArithmeticExactSequenceRationalFactProvider20261018 originalNormKernelRanksTwoPiKernelFiniteProvider20261018 originalNormKernelRanksTwoConjugateKernelFiniteProvider20261018
attribute [local instance] MazurTransfer.Order13ActualNormCharacterH1Exactness.actualNormCharacterH1ExactnessDataProvider520261018 MazurTransfer.Order13ActualNormCharacterH1Exactness.actualNormCharacterH1ExactnessDataProvider620261018 MazurTransfer.Order13ActualNormCharacterH1Exactness.actualNormCharacterH1ExactnessDataProvider720261018 MazurTransfer.Order13ActualNormCharacterH1Exactness.actualNormCharacterH1ExactnessDataProvider820261018
open Order13ActualNormCharacterContinuousH1 Order13ActualNormCharacterKummerUnramified
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualOrderedCharacterContinuousH1
attribute [local instance] Order13ActualOrderedCharacterContinuousH1.orderedContinuousOriginalPiKernelActionProvider20261019 Order13ActualOrderedCharacterContinuousH1.orderedContinuousOriginalConjugateKernelActionProvider20261019
open OneDimensionalSelectedQuotientKernel
open Order13ActualSelectedCharacterExactSequences
theorem solution :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) ,
    ∃ i : Representation.IntertwiningMap
        (ScalarCharacterLine.scalarRepresentation (piConjugateReflectedCharacter K z hz))
        (kernelRepresentation K schemePi),
      Function.Injective i ∧ LinearMap.range i.toLinearMap = LinearMap.ker (piQuotient K z hz 𝒱).toLinearMap) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) ,
    ∃ i : Representation.IntertwiningMap
        (Representation.trivial (ZMod 19) (K ≃ₐ[ℚ] K) (ZMod 19))
        (kernelRepresentation K schemePiConjugate),
      Function.Injective i ∧
        LinearMap.range i.toLinearMap = LinearMap.ker (piConjugateQuotient K z hz 𝒱).toLinearMap) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) , Function.Injective (selectedPiInclusion K z hz 𝒱)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) ,
    LinearMap.range (selectedPiInclusion K z hz 𝒱).toLinearMap =
      LinearMap.ker (piQuotient K z hz 𝒱).toLinearMap) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) , Function.Injective (selectedPiConjugateInclusion K z hz 𝒱)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) ,
    LinearMap.range (selectedPiConjugateInclusion K z hz 𝒱).toLinearMap =
      LinearMap.ker (piConjugateQuotient K z hz 𝒱).toLinearMap) := by
  exact ⟨MazurTransfer.Order13ActualSelectedCharacterExactSequences.exists_pi_selected_kernel_inclusion,MazurTransfer.Order13ActualSelectedCharacterExactSequences.exists_piConjugate_selected_kernel_inclusion,MazurTransfer.Order13ActualSelectedCharacterExactSequences.selectedPiInclusion_injective,MazurTransfer.Order13ActualSelectedCharacterExactSequences.selectedPiInclusion_range,MazurTransfer.Order13ActualSelectedCharacterExactSequences.selectedPiConjugateInclusion_injective,MazurTransfer.Order13ActualSelectedCharacterExactSequences.selectedPiConjugateInclusion_range⟩
#print axioms solution
