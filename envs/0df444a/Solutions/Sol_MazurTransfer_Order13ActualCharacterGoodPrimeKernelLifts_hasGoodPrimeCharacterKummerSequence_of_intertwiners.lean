-- Prove2me | solution 1 for MazurTransfer.Order13ActualCharacterGoodPrimeKernelLifts.hasGoodPrimeCharacterKummerSequence_of_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T01:33:14.472115+00:00
-- url     : https://prove2.me/submissions/064e8255-eb3f-4b76-96be-c48b191f89fe

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual character-line lifts of norm Kummer classes are
unramified on every genuine good-prime valuation inertia subgroup.
Named downstream consumer: character Selmer bounds for the actual norm images.
-/
import Definitions.Def_MazurTransfer_Order13ActualCharacterGoodPrimeKernelLiftsOriginalData20261019
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyTrivialTargetInjection_coefficientMap_injective
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelGoodPrimeInertia_kernel_inertia_fixed
import Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerKernelControl_normQuotient_image_zero_iff_character_lift
import Theorems.Thm_MazurTransfer_Order13GoodPrimeUnramifiedKummer_continuous_norm_class_unramified
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerUnramified
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualCharacterGoodPrimeKernelLifts
attribute [local instance] actualCharacterGoodPrimeKernelLiftsOriginalProvider120261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider220261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider320261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider420261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider520261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider620261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider720261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider820261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider920261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider1020261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider1120261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider1220261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider1320261019 actualCharacterGoodPrimeKernelLiftsOriginalProvider1420261019
namespace MazurTransfer.ActualCharacterGoodPrimeKernelLiftsProofHelpers20261019
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj





open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]








open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]



open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
variable {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
  [AddCommGroup V] [Module (ZMod 19) V]
variable (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
  (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)



open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerUnramified
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection


variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19)
variable (hφ : φ = schemePi ∨ φ = schemePiConjugate)
variable (A : ValuationSubring K) (hA : A.LiesOverPrime q)
include hq hne hφ hA

theorem localInclusionClass_injective (hi : Function.Injective i) :
    Function.Injective (localInclusionClass K φ σ i (A.inertiaSubgroupIn ℚ)) := by
  apply ContinuousFirstCohomologyTrivialTargetInjection.coefficientMap_injective
    (A.inertiaSubgroupIn ℚ) (Coefficient σ) (Kernel K φ)
    (toIntertwining σ (kernelRepresentation K φ) i)
    (toIntertwining_injective σ (kernelRepresentation K φ) i hi)
    (fun s x => toIntertwining_equivariant σ (kernelRepresentation K φ) i
      (by intro g m; rfl) s.val x) continuous_of_discreteTopology
  intro s x
  exact Order13ActualNormKernelGoodPrimeInertia.kernel_inertia_fixed K φ q hq hne hφ A hA s.val s.property x

theorem character_lift_unramified
    (hi : Function.Injective i)
    (y : ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ))
    (x : ContinuousH1 K φ) (hy : inclusionClass K φ σ i y = x)
    (hx : restrictionLinearMap K φ (A.inertiaSubgroupIn ℚ) x = 0) :
    coefficientRestriction K σ (A.inertiaSubgroupIn ℚ) y = 0 := by
  apply localInclusionClass_injective K φ σ i q hq hne hφ A hA hi
  rw [map_zero, ← restriction_inclusionClass, hy, hx]

omit hq hne hA in
 theorem normQuotient_kernel_lifts_to_goodPrimeClasses
    (hsurj : Function.Surjective (normHom K φ))
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap)
    (x : NormQuotient φ) (hx : normQuotientCharacterHom K φ τ p hsurj x = 1) :
    ∃ y ∈ goodPrimeClasses K σ,
      inclusionClass K φ σ i y = (continuousQuotientHom K φ hsurj x).toAdd := by
  obtain ⟨y, hy⟩ := (Order13ActualNormCharacterKummerKernelControl.normQuotient_image_zero_iff_character_lift
    K φ σ τ i p hsurj hi hp hk x).mp hx
  refine ⟨y, ?_, hy⟩
  intro q hq hgood hne A hA
  apply character_lift_unramified K φ σ i q hgood hne hφ A hA hi y _ hy
  refine Quotient.inductionOn x ?_
  intro a
  exact Order13GoodPrimeUnramifiedKummer.continuous_norm_class_unramified
    q hgood hne K φ hφ A hA a (chosenLift K φ hsurj a) (chosenLift_spec K φ hsurj a)

omit hq hne hA in
 theorem hasGoodPrimeCharacterKummerSequence_of_intertwiners
    (hsurj : Function.Surjective (normHom K φ))
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    HasGoodPrimeCharacterKummerSequence K φ σ τ hsurj :=
  ⟨i, p, hi, hp, hk, range_inclusionClass_eq_ker_mapClass K φ σ τ i p hi hp hk,
    fun x hx => normQuotient_kernel_lifts_to_goodPrimeClasses K φ σ τ i p hφ hsurj hi hp hk x hx⟩

end MazurTransfer.ActualCharacterGoodPrimeKernelLiftsProofHelpers20261019
theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
    {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
    [AddCommGroup V] [Module (ZMod 19) V]
    (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
    (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
    (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
    (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (hsurj : Function.Surjective (normHom K φ))
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    HasGoodPrimeCharacterKummerSequence K φ σ τ hsurj := by
  exact MazurTransfer.ActualCharacterGoodPrimeKernelLiftsProofHelpers20261019.hasGoodPrimeCharacterKummerSequence_of_intertwiners K φ σ τ i p hφ hsurj hi hp hk
#print axioms solution
