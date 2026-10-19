-- Prove2me | solution 1 for MazurTransfer.order13_actual_ordered_continuous_h1_and_kummer_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T02:10:08.660309+00:00
-- url     : https://prove2.me/submissions/5ae5c13d-9987-4777-a9d7-288b711c867e

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: instantiate the continuous H1 and Kummer pushforwards with
the SAME actual ordered norm quotients: pi to literal mu19, and conjugate pi
to mu19 twisted by chi13 inverse. Named downstream consumer: exceptional-prime
local Kummer conditions and global norm Selmer bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualOrderedCharacterContinuousH1OriginalChosenQuotientsAndKummerDataFixedKernelActionsAndContinuousNamespacesV320261019
import Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerUnramified_normQuotientCharacterHom_unramified
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
namespace MazurTransfer.ActualOrderedContinuousH1KummerProofHelpers20261019
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)
include z hz 𝒱
variable (S : Subgroup (K ≃ₐ[ℚ] K))
theorem pi_restriction_mapClass (x : ContinuousH1 K schemePi) :
    coefficientRestriction K (rootsRepresentation K) S (piMapClass K z hz 𝒱 x) =
    localMapClass K schemePi (rootsRepresentation K) (piQuotient K z hz 𝒱) S
      (Order13ActualPicardNormSubgroupRestrictionF19.restrictionLinearMap K schemePi S x) :=
  restriction_mapClass K schemePi (rootsRepresentation K) (piQuotient K z hz 𝒱) S x

theorem piConjugate_restriction_mapClass (x : ContinuousH1 K schemePiConjugate) :
    coefficientRestriction K (twistedRootsRepresentation K z hz) S (piConjugateMapClass K z hz 𝒱 x) =
    localMapClass K schemePiConjugate (twistedRootsRepresentation K z hz) (piConjugateQuotient K z hz 𝒱) S
      (Order13ActualPicardNormSubgroupRestrictionF19.restrictionLinearMap K schemePiConjugate S x) :=
  restriction_mapClass K schemePiConjugate (twistedRootsRepresentation K z hz) (piConjugateQuotient K z hz 𝒱) S x

variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
variable (A : ValuationSubring K) (hA : A.LiesOverPrime q)
include hq hne hA
theorem piKummerHom_unramified (x : NormQuotient schemePi) :
    coefficientRestriction K (rootsRepresentation K) (A.inertiaSubgroupIn ℚ)
      (piKummerHom K z hz 𝒱 x).toAdd = 0 :=
  normQuotientCharacterHom_unramified K schemePi (rootsRepresentation K) (piQuotient K z hz 𝒱)
    (schemePi_geometricPoint_surjective K) q hq hne (Or.inl rfl) A hA x

theorem piConjugateKummerHom_unramified (x : NormQuotient schemePiConjugate) :
    coefficientRestriction K (twistedRootsRepresentation K z hz) (A.inertiaSubgroupIn ℚ)
      (piConjugateKummerHom K z hz 𝒱 x).toAdd = 0 :=
  normQuotientCharacterHom_unramified K schemePiConjugate (twistedRootsRepresentation K z hz)
    (piConjugateQuotient K z hz 𝒱) (schemePiConjugate_geometricPoint_surjective K)
    q hq hne (Or.inr rfl) A hA x

end MazurTransfer.ActualOrderedContinuousH1KummerProofHelpers20261019
theorem solution :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) , Function.Surjective (piQuotient K z hz 𝒱)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) , Function.Surjective (piConjugateQuotient K z hz 𝒱)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) , ContinuousSMul (K ≃ₐ[ℚ] K) (Coefficient (rootsRepresentation K))) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) ,
    ContinuousSMul (K ≃ₐ[ℚ] K) (Coefficient (twistedRootsRepresentation K z hz))) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (S : Subgroup (K ≃ₐ[ℚ] K)) (x : ContinuousH1 K schemePi) ,
    coefficientRestriction K (rootsRepresentation K) S (piMapClass K z hz 𝒱 x) =
    localMapClass K schemePi (rootsRepresentation K) (piQuotient K z hz 𝒱) S
      (Order13ActualPicardNormSubgroupRestrictionF19.restrictionLinearMap K schemePi S x)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (S : Subgroup (K ≃ₐ[ℚ] K)) (x : ContinuousH1 K schemePiConjugate) ,
    coefficientRestriction K (twistedRootsRepresentation K z hz) S (piConjugateMapClass K z hz 𝒱 x) =
    localMapClass K schemePiConjugate (twistedRootsRepresentation K z hz) (piConjugateQuotient K z hz 𝒱) S
      (Order13ActualPicardNormSubgroupRestrictionF19.restrictionLinearMap K schemePiConjugate S x)) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) (A : ValuationSubring K) (hA : A.LiesOverPrime q) (x : NormQuotient schemePi) ,
    coefficientRestriction K (rootsRepresentation K) (A.inertiaSubgroupIn ℚ)
      (piKummerHom K z hz 𝒱 x).toAdd = 0) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) (A : ValuationSubring K) (hA : A.LiesOverPrime q) (x : NormQuotient schemePiConjugate) ,
    coefficientRestriction K (twistedRootsRepresentation K z hz) (A.inertiaSubgroupIn ℚ)
      (piConjugateKummerHom K z hz 𝒱 x).toAdd = 0) := by
  exact ⟨MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piQuotient_surjective, MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piConjugateQuotient_surjective, MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piCoefficient_continuousSMul, MazurTransfer.Order13ActualOrderedCharacterContinuousH1.piConjugateCoefficient_continuousSMul, MazurTransfer.ActualOrderedContinuousH1KummerProofHelpers20261019.pi_restriction_mapClass, MazurTransfer.ActualOrderedContinuousH1KummerProofHelpers20261019.piConjugate_restriction_mapClass, MazurTransfer.ActualOrderedContinuousH1KummerProofHelpers20261019.piKummerHom_unramified, MazurTransfer.ActualOrderedContinuousH1KummerProofHelpers20261019.piConjugateKummerHom_unramified⟩
#print axioms solution
