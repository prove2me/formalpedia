-- Prove2me | solution 1 for MazurTransfer.order13_character_kernel_lifts_unramified_away_thirteen_nineteen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T12:51:00.424996+00:00
-- url     : https://prove2.me/submissions/9a971416-5d4d-4bbf-a74d-aa6600e084a1

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: lift actual norm-character Kummer kernels through the same exact inclusion into classes unramified at every genuine valuation inertia group away from 13 and 19, including 2.
Named downstream consumer: selected-character unramified kernel lifts and actual norm Selmer bounds.
-/
import Definitions.Def_MazurTransfer_Order13OriginalUnramifiedCharacterClassSubmoduleAndSequenceData20261019
import Theorems.Thm_MazurTransfer_order13_all_prime_norm_kummer_and_kernel_inertia
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyTrivialTargetInjection_coefficientMap_injective
import Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerKernelControl_normQuotient_image_zero_iff_character_lift
noncomputable section
open MazurTransfer
open Order13ActualCharacterKernelLiftsAwayThirteenNineteen
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
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instTopologicalSpacePoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instDiscreteTopologyPoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instMulActionAlgEquivRatPoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatContinuousH1_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen_1
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatH1SubtypeAlgEquivRatMemSubgroupCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen
namespace MazurTransfer.UnramifiedCharacterKernelLiftProofBoundary20261019
end MazurTransfer.UnramifiedCharacterKernelLiftProofBoundary20261019
namespace MazurTransfer.UnramifiedCharacterKernelPublicBridges20261019
theorem kernel_inertia_fixed (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (z : Kernel K φ) :
    σ • z = z :=
  MazurTransfer.order13_all_prime_norm_kummer_and_kernel_inertia.2.2.1 K φ q h13 h19 hφ A hA σ hσ z
theorem continuous_norm_class_unramified (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19) [IsGalois ℚ K] [IsFinite φ.left]
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime q)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    restrictNormClass K φ (A.inertiaSubgroupIn ℚ)
      (continuousClassOfLift K φ a b hb) = 0 :=
  MazurTransfer.order13_all_prime_norm_kummer_and_kernel_inertia.2.1 K φ q h13 h19 hφ A hA a b hb
end MazurTransfer.UnramifiedCharacterKernelPublicBridges20261019

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual character-line lifts of norm Kummer classes are
unramified on every genuine valuation inertia subgroup away from thirteen and nineteen.
The dyadic case and all odd good primes use the SAME fixed norm kernels
and the original exact cohomology maps. No splitting is assumed.
Named downstream consumer: character Selmer bounds for the actual norm images.
-/

noncomputable section
namespace MazurTransfer.UnramifiedCharacterKernelLiftProof20261019
open Order13ActualCharacterKernelLiftsAwayThirteenNineteen
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualCharacterKernelLiftsAwayThirteenNineteen

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]

attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instTopologicalSpacePoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instDiscreteTopologyPoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instMulActionAlgEquivRatPoints_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatContinuousH1_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13ActualCharacterKernelLiftsAwayThirteenNineteen
open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
variable {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
  [AddCommGroup V] [Module (ZMod 19) V]
variable (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
  (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatH1AlgEquivRatCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen_1

open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerUnramified
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
attribute [local instance] MazurTransfer.Order13ActualCharacterKernelLiftsAwayThirteenNineteen.instModuleZModOfNatNatH1SubtypeAlgEquivRatMemSubgroupCoefficient_order13ActualCharacterKernelLiftsAwayThirteenNineteen

variable (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19)
variable (hφ : φ = schemePi ∨ φ = schemePiConjugate)
variable (A : ValuationSubring K) (hA : A.LiesOverPrime q)
include h13 h19 hφ hA

theorem localInclusionClass_injective (hi : Function.Injective i) :
    Function.Injective (localInclusionClass K φ σ i (A.inertiaSubgroupIn ℚ)) := by
  apply ContinuousFirstCohomologyTrivialTargetInjection.coefficientMap_injective
    (A.inertiaSubgroupIn ℚ) (Coefficient σ) (Kernel K φ)
    (toIntertwining σ (kernelRepresentation K φ) i)
    (toIntertwining_injective σ (kernelRepresentation K φ) i hi)
    (fun s x => toIntertwining_equivariant σ (kernelRepresentation K φ) i
      (by intro g m; rfl) s.val x) continuous_of_discreteTopology
  intro s x
  exact MazurTransfer.UnramifiedCharacterKernelPublicBridges20261019.kernel_inertia_fixed K φ q h13 h19 hφ A hA s.val s.property x

theorem character_lift_unramified
    (hi : Function.Injective i)
    (y : ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ))
    (x : ContinuousH1 K φ) (hy : inclusionClass K φ σ i y = x)
    (hx : restrictionLinearMap K φ (A.inertiaSubgroupIn ℚ) x = 0) :
    coefficientRestriction K σ (A.inertiaSubgroupIn ℚ) y = 0 := by
  apply localInclusionClass_injective K φ σ i q h13 h19 hφ A hA hi
  rw [map_zero, ← restriction_inclusionClass, hy, hx]



omit h13 h19 hA in
 theorem normQuotient_kernel_lifts_to_unramifiedClassesAwayThirteenNineteen
    (hsurj : Function.Surjective (normHom K φ))
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap)
    (x : NormQuotient φ) (hx : normQuotientCharacterHom K φ τ p hsurj x = 1) :
    ∃ y ∈ unramifiedClassesAwayThirteenNineteen K σ,
      inclusionClass K φ σ i y = (continuousQuotientHom K φ hsurj x).toAdd := by
  obtain ⟨y, hy⟩ := (Order13ActualNormCharacterKummerKernelControl.normQuotient_image_zero_iff_character_lift
    K φ σ τ i p hsurj hi hp hk x).mp hx
  refine ⟨y, ?_, hy⟩
  intro q h13 hgood h19 A hA
  apply character_lift_unramified K φ σ i q hgood h19 hφ A hA hi y _ hy
  refine Quotient.inductionOn x ?_
  intro a
  exact MazurTransfer.UnramifiedCharacterKernelPublicBridges20261019.continuous_norm_class_unramified
    K φ q hgood h19 hφ A hA a (chosenLift K φ hsurj a) (chosenLift_spec K φ hsurj a)



omit h13 h19 hA in
 theorem hasUnramifiedAwayThirteenNineteenCharacterKummerSequence_of_intertwiners
    (hsurj : Function.Surjective (normHom K φ))
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    HasUnramifiedAwayThirteenNineteenCharacterKummerSequence K φ σ τ hsurj :=
  ⟨i, p, hi, hp, hk, range_inclusionClass_eq_ker_mapClass K φ σ τ i p hi hp hk,
    fun x hx => normQuotient_kernel_lifts_to_unramifiedClassesAwayThirteenNineteen K φ σ τ i p hφ hsurj hi hp hk x hx⟩

end MazurTransfer.UnramifiedCharacterKernelLiftProof20261019

end
theorem solution : (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {U : Type} [AddCommGroup U] [Module (ZMod 19) U] (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U) (i : Representation.IntertwiningMap σ (kernelRepresentation K φ)) (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19) (hφ : φ = schemePi ∨ φ = schemePiConjugate) (A : ValuationSubring K) (hA : A.LiesOverPrime q), ∀ (hi : Function.Injective i), Function.Injective (localInclusionClass K φ σ i (A.inertiaSubgroupIn ℚ))) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {U : Type} [AddCommGroup U] [Module (ZMod 19) U] (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U) (i : Representation.IntertwiningMap σ (kernelRepresentation K φ)) (q : ℕ) [Fact q.Prime] (h13 : q ≠ 13) (h19 : q ≠ 19) (hφ : φ = schemePi ∨ φ = schemePiConjugate) (A : ValuationSubring K) (hA : A.LiesOverPrime q), ∀ (hi : Function.Injective i)
    (y : ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ))
    (x : ContinuousH1 K φ) (hy : inclusionClass K φ σ i y = x)
    (hx : restrictionLinearMap K φ (A.inertiaSubgroupIn ℚ) x = 0), coefficientRestriction K σ (A.inertiaSubgroupIn ℚ) y = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {U V : Type} [AddCommGroup U] [Module (ZMod 19) U] [AddCommGroup V] [Module (ZMod 19) V] (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U) (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (i : Representation.IntertwiningMap σ (kernelRepresentation K φ)) (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hφ : φ = schemePi ∨ φ = schemePiConjugate), ∀ (hsurj : Function.Surjective (normHom K φ))
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap)
    (x : NormQuotient φ) (hx : normQuotientCharacterHom K φ τ p hsurj x = 1), ∃ y ∈ unramifiedClassesAwayThirteenNineteen K σ,
      inclusionClass K φ σ i y = (continuousQuotientHom K φ hsurj x).toAdd) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {U V : Type} [AddCommGroup U] [Module (ZMod 19) U] [AddCommGroup V] [Module (ZMod 19) V] (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U) (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (i : Representation.IntertwiningMap σ (kernelRepresentation K φ)) (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hφ : φ = schemePi ∨ φ = schemePiConjugate), ∀ (hsurj : Function.Surjective (normHom K φ))
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap), HasUnramifiedAwayThirteenNineteenCharacterKummerSequence K φ σ τ hsurj) := by
  exact ⟨MazurTransfer.UnramifiedCharacterKernelLiftProof20261019.localInclusionClass_injective, MazurTransfer.UnramifiedCharacterKernelLiftProof20261019.character_lift_unramified, MazurTransfer.UnramifiedCharacterKernelLiftProof20261019.normQuotient_kernel_lifts_to_unramifiedClassesAwayThirteenNineteen, MazurTransfer.UnramifiedCharacterKernelLiftProof20261019.hasUnramifiedAwayThirteenNineteenCharacterKummerSequence_of_intertwiners⟩
#print axioms solution
