-- Prove2me | solution 1 for MazurTransfer.order13_character_norm_kummer_dyadic_and_all_prime_local_conditions
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T12:06:39.874166+00:00
-- url     : https://prove2.me/submissions/bb898213-468c-4847-867d-3f8826457f16

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same actual norm-character pushforward and norm quotient maps have zero genuine inertia restriction at 2 and every prime except 13 and 19.
Named downstream consumer: the previously selected ordered character maps and actual Selmer dimensions.
-/
import Definitions.Def_MazurTransfer_Order13OriginalCharacterLocalConditionScopedTopologyAndModuleData20261019
import Theorems.Thm_MazurTransfer_order13_all_prime_norm_kummer_and_kernel_inertia
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardSchemeNormGroupHom Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelF19Representation Order13ActualNormCharacterKummerUnramified
open Order13ActualNormCharacterContinuousH1 Order13ActualPicardNormContinuousCohomology
open Order13ActualPicardNormContinuousCocycles Order13ActualPicardNormAlgebraicKummerInjection
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instTopologicalSpacePoints_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instDiscreteTopologyPoints_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instMulActionAlgEquivRatPoints_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instModuleZModOfNatNatContinuousH1_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualNormCharacterDyadicKummerConditions
namespace MazurTransfer.CharacterNormLocalConditionsProofBoundary20261019
end MazurTransfer.CharacterNormLocalConditionsProofBoundary20261019
namespace MazurTransfer.CharacterLocalKummerBridges20261019
theorem dyadic_continuous_norm_class_unramified (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsGalois ℚ K] [IsFinite φ.left]
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime 2)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    MazurTransfer.Order13ActualPicardNormSubgroupRestriction.restrictNormClass K φ (A.inertiaSubgroupIn ℚ)
      (continuousClassOfLift K φ a b hb) = 0 :=
  MazurTransfer.order13_actual_dyadic_continuous_norm_kummer_and_fixed_quotient_unramified.2.1 K φ hφ A hA a b hb
theorem all_prime_continuous_norm_class_unramified (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19) [IsGalois ℚ K] [IsFinite φ.left]
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    MazurTransfer.Order13ActualPicardNormSubgroupRestriction.restrictNormClass K φ (A.inertiaSubgroupIn ℚ)
      (continuousClassOfLift K φ a b hb) = 0 :=
  MazurTransfer.order13_all_prime_norm_kummer_and_kernel_inertia.2.1 K φ q h13 h19 hφ A hA a b hb
end MazurTransfer.CharacterLocalKummerBridges20261019

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: preserve the EXISTING fixed norm-character Kummer map
and prove zero valuation-inertia restriction at TWO and every prime away
from thirteen and nineteen. No injectivity of coefficient pushforward
and no splitting of the actual character extensions is assumed.
Named downstream consumer: ordered actual character Selmer images and
exceptional local conditions at thirteen and nineteen.
-/

noncomputable section
namespace MazurTransfer.CharacterNormLocalConditionsTheoremBody20261019
open Order13ActualNormCharacterDyadicKummerConditions
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualNormCharacterDyadicKummerConditions

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]

attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instTopologicalSpacePoints_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instDiscreteTopologyPoints_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instMulActionAlgEquivRatPoints_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instModuleZModOfNatNatContinuousH1_order13ActualNormCharacterDyadicKummerConditions
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualNormCharacterDyadicKummerConditions
variable {V : Type} [AddCommGroup V] [Module (ZMod 19) V]
variable (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
attribute [local instance] MazurTransfer.Order13ActualNormCharacterDyadicKummerConditions.instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualNormCharacterDyadicKummerConditions

open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualNormCharacterContinuousH1
variable (hsurj : Function.Surjective (normHom K φ))

open Order13ActualNormCharacterKummerUnramified

variable (hφ : φ = schemePi ∨ φ = schemePiConjugate)
include hφ

theorem pushed_norm_class_dyadic_unramified
    (A : ValuationSubring K) (hA : A.LiesOverPrime 2)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (mapClass K φ τ f (continuousClassOfLift K φ a b hb)) = 0 := by
  apply restriction_zero_of_source_zero
  exact MazurTransfer.CharacterLocalKummerBridges20261019.dyadic_continuous_norm_class_unramified
    K φ hφ A hA a b hb

theorem normQuotientCharacterHom_dyadic_unramified
    (A : ValuationSubring K) (hA : A.LiesOverPrime 2) (x : NormQuotient φ) :
    coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (normQuotientCharacterHom K φ τ f hsurj x).toAdd = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  rw [normQuotientCharacterHom_apply]
  exact pushed_norm_class_dyadic_unramified K φ τ f hφ A hA a
    (chosenLift K φ hsurj a) (chosenLift_spec K φ hsurj a)

variable (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
include h13 h19

theorem pushed_norm_class_unramified_away_thirteen_nineteen
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (mapClass K φ τ f (continuousClassOfLift K φ a b hb)) = 0 := by
  apply restriction_zero_of_source_zero
  exact MazurTransfer.CharacterLocalKummerBridges20261019.all_prime_continuous_norm_class_unramified
    K φ q h13 h19 hφ A hA a b hb

theorem normQuotientCharacterHom_unramified_away_thirteen_nineteen
    (A : ValuationSubring K) (hA : A.LiesOverPrime q) (x : NormQuotient φ) :
    coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (normQuotientCharacterHom K φ τ f hsurj x).toAdd = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  rw [normQuotientCharacterHom_apply]
  exact pushed_norm_class_unramified_away_thirteen_nineteen K φ τ f hφ q h13 h19 A hA a
    (chosenLift K φ hsurj a) (chosenLift_spec K φ hsurj a)

end MazurTransfer.CharacterNormLocalConditionsTheoremBody20261019

end
theorem solution : (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {V : Type} [AddCommGroup V] [Module (ZMod 19) V] (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hφ : φ = schemePi ∨ φ = schemePiConjugate), ∀ (A : ValuationSubring K) (hA : A.LiesOverPrime 2)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a), coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (mapClass K φ τ f (continuousClassOfLift K φ a b hb)) = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {V : Type} [AddCommGroup V] [Module (ZMod 19) V] (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hsurj : Function.Surjective (normHom K φ)) (hφ : φ = schemePi ∨ φ = schemePiConjugate), ∀ (A : ValuationSubring K) (hA : A.LiesOverPrime 2) (x : NormQuotient φ), coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (normQuotientCharacterHom K φ τ f hsurj x).toAdd = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {V : Type} [AddCommGroup V] [Module (ZMod 19) V] (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hφ : φ = schemePi ∨ φ = schemePiConjugate) (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19), ∀ (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a), coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (mapClass K φ τ f (continuousClassOfLift K φ a b hb)) = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {V : Type} [AddCommGroup V] [Module (ZMod 19) V] (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (f : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hsurj : Function.Surjective (normHom K φ)) (hφ : φ = schemePi ∨ φ = schemePiConjugate) (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19), ∀ (A : ValuationSubring K) (hA : A.LiesOverPrime q) (x : NormQuotient φ), coefficientRestriction K τ (A.inertiaSubgroupIn ℚ)
      (normQuotientCharacterHom K φ τ f hsurj x).toAdd = 0) := by
  exact ⟨MazurTransfer.CharacterNormLocalConditionsTheoremBody20261019.pushed_norm_class_dyadic_unramified, MazurTransfer.CharacterNormLocalConditionsTheoremBody20261019.normQuotientCharacterHom_dyadic_unramified, MazurTransfer.CharacterNormLocalConditionsTheoremBody20261019.pushed_norm_class_unramified_away_thirteen_nineteen, MazurTransfer.CharacterNormLocalConditionsTheoremBody20261019.normQuotientCharacterHom_unramified_away_thirteen_nineteen⟩
#print axioms solution
