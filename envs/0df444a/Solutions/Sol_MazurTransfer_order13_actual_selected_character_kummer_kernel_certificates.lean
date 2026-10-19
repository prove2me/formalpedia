-- Prove2me | solution 1 for MazurTransfer.order13_actual_selected_character_kummer_kernel_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T04:00:50.569603+00:00
-- url     : https://prove2.me/submissions/04d5780e-9990-4e21-8667-223e61de5242

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the kernels of BOTH original selected continuous-H1
character maps are the ranges of the character inclusions now proved
compatible with their SAME selected quotients. Give the corresponding
exact criterion for zero under the ORIGINAL norm-character Kummer maps.
Named downstream consumer: arithmetic control of the kernel of coefficient
pushforward before using the checked pi character image dimension bound.
-/
import Definitions.Def_MazurTransfer_Order13ActualOrderedCharacterContinuousH1OriginalChosenQuotientsAndKummerDataFixedKernelActionsAndContinuousNamespacesV320261019
import Theorems.Thm_MazurTransfer_OneDimensionalSelectedQuotientKernel_exists_injective_with_selected_kernel
import Theorems.Thm_MazurTransfer_order13_actual_ordered_arithmetic_character_sequence_certificates
import Definitions.Def_MazurTransfer_Order13ActualSelectedCharacterOriginalCoherentInclusionData20261019
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterH1GlobalExactnessBridgeData
import Definitions.Def_MazurTransfer_Order13ActualSelectedCharacterOriginalH1InclusionData20261019
import Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerKernelControl_normQuotient_image_zero_iff_character_lift
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
attribute [local instance] Order13ActualSelectedCharacterExactSequences.selectedCharacterOriginalRootsFiniteDimProvider20261019
open Order13ActualSelectedCharacterKummerKernel
open Order13ActualPicardNormContinuousKummerInjection
attribute [local instance] Order13ActualSelectedCharacterKummerKernel.selectedCharacterH1OriginalProvider120261019 Order13ActualSelectedCharacterKummerKernel.selectedCharacterH1OriginalProvider220261019 Order13ActualSelectedCharacterKummerKernel.selectedCharacterH1OriginalProvider320261019 Order13ActualSelectedCharacterKummerKernel.selectedCharacterH1OriginalProvider420261019 Order13ActualSelectedCharacterKummerKernel.selectedCharacterH1OriginalProvider520261019 Order13ActualSelectedCharacterKummerKernel.selectedCharacterH1OriginalProvider620261019 Order13ActualSelectedCharacterKummerKernel.selectedCharacterH1OriginalProvider720261019 Order13ActualSelectedCharacterKummerKernel.selectedCharacterH1OriginalProvider820261019
namespace MazurTransfer.Order13ActualSelectedCharacterKummerKernel
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)
theorem piInclusionClass_range : LinearMap.range (piInclusionClass K z hz 𝒱) =
    LinearMap.ker (piMapClass K z hz 𝒱) :=
  range_inclusionClass_eq_ker_mapClass K schemePi (piLineRepresentation K z hz) (rootsRepresentation K)
    (selectedPiInclusion K z hz 𝒱) (piQuotient K z hz 𝒱)
    (selectedPiInclusion_injective K z hz 𝒱) (piQuotient_surjective K z hz 𝒱)
    (selectedPiInclusion_range K z hz 𝒱)

theorem piConjugateInclusionClass_range : LinearMap.range (piConjugateInclusionClass K z hz 𝒱) =
    LinearMap.ker (piConjugateMapClass K z hz 𝒱) :=
  range_inclusionClass_eq_ker_mapClass K schemePiConjugate (trivialLineRepresentation K)
    (twistedRootsRepresentation K z hz) (selectedPiConjugateInclusion K z hz 𝒱)
    (piConjugateQuotient K z hz 𝒱) (selectedPiConjugateInclusion_injective K z hz 𝒱)
    (piConjugateQuotient_surjective K z hz 𝒱) (selectedPiConjugateInclusion_range K z hz 𝒱)

theorem piKummerHom_eq_one_iff_character_lift (x : NormQuotient schemePi) :
    piKummerHom K z hz 𝒱 x = 1 ↔ ∃ y : (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient (piLineRepresentation K z hz))),
      piInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePi (schemePi_geometricPoint_surjective K) x).toAdd :=
  normQuotient_image_zero_iff_character_lift K schemePi (piLineRepresentation K z hz)
    (rootsRepresentation K) (selectedPiInclusion K z hz 𝒱) (piQuotient K z hz 𝒱)
    (schemePi_geometricPoint_surjective K) (selectedPiInclusion_injective K z hz 𝒱)
    (piQuotient_surjective K z hz 𝒱) (selectedPiInclusion_range K z hz 𝒱) x

theorem piConjugateKummerHom_eq_one_iff_character_lift (x : NormQuotient schemePiConjugate) :
    piConjugateKummerHom K z hz 𝒱 x = 1 ↔ ∃ y : (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient (trivialLineRepresentation K))),
      piConjugateInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePiConjugate (schemePiConjugate_geometricPoint_surjective K) x).toAdd :=
  normQuotient_image_zero_iff_character_lift K schemePiConjugate (trivialLineRepresentation K)
    (twistedRootsRepresentation K z hz) (selectedPiConjugateInclusion K z hz 𝒱)
    (piConjugateQuotient K z hz 𝒱) (schemePiConjugate_geometricPoint_surjective K)
    (selectedPiConjugateInclusion_injective K z hz 𝒱) (piConjugateQuotient_surjective K z hz 𝒱)
    (selectedPiConjugateInclusion_range K z hz 𝒱) x

end MazurTransfer.Order13ActualSelectedCharacterKummerKernel
theorem solution :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) , LinearMap.range (piInclusionClass K z hz 𝒱) =
    LinearMap.ker (piMapClass K z hz 𝒱)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) , LinearMap.range (piConjugateInclusionClass K z hz 𝒱) =
    LinearMap.ker (piConjugateMapClass K z hz 𝒱)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (x : NormQuotient schemePi) ,
    piKummerHom K z hz 𝒱 x = 1 ↔ ∃ y : (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient (piLineRepresentation K z hz))),
      piInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePi (schemePi_geometricPoint_surjective K) x).toAdd) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (x : NormQuotient schemePiConjugate) ,
    piConjugateKummerHom K z hz 𝒱 x = 1 ↔ ∃ y : (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient (trivialLineRepresentation K))),
      piConjugateInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePiConjugate (schemePiConjugate_geometricPoint_surjective K) x).toAdd) := by
  exact ⟨MazurTransfer.Order13ActualSelectedCharacterKummerKernel.piInclusionClass_range,MazurTransfer.Order13ActualSelectedCharacterKummerKernel.piConjugateInclusionClass_range,MazurTransfer.Order13ActualSelectedCharacterKummerKernel.piKummerHom_eq_one_iff_character_lift,MazurTransfer.Order13ActualSelectedCharacterKummerKernel.piConjugateKummerHom_eq_one_iff_character_lift⟩
#print axioms solution
