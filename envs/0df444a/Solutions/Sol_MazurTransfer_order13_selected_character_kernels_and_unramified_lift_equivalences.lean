-- Prove2me | solution 1 for MazurTransfer.order13_selected_character_kernels_and_unramified_lift_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T13:14:04.404736+00:00
-- url     : https://prove2.me/submissions/ce38a968-017d-445e-8cc8-87547fefcd59

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: zero under each previously selected norm-character Kummer map is equivalent to a lift through its same original character inclusion in the original submodule unramified on EVERY genuine inertia group away from 13 and 19, including 2.
Named downstream consumer: actual selected-character kernel dimensions and norm Selmer bounds.
-/
import Definitions.Def_MazurTransfer_Order13OriginalSelectedUnramifiedCharacterClassSubmodulesData20261019
import Theorems.Thm_MazurTransfer_order13_character_kernel_lifts_unramified_away_thirteen_nineteen
import Theorems.Thm_MazurTransfer_order13_actual_selected_character_kummer_kernel_certificates
noncomputable section
open MazurTransfer
open Order13ActualSelectedCharacterUnramifiedKernelLifts
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
open Order13ActualNormKernelF19Representation Order13ActualNormFixedKernelEquivalence
open Order13ActualNormKernelFiniteModule
open Order13ActualPicardSchemeNineteenNorm Order13ActualNormKernelFiniteModule
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelCrossPairing
open NineteenRootsGaloisRepresentation Order13ActualNineteenTorsionNormPairingAdjoint
open Order13ActualNormKernelInvariantDimensions Order13ActualComplementaryCharacterExactSequence
open Order13ActualArithmeticCharacterExactSequence Order13ActualCyclotomicThirteenKernelCharacter
open Order13ActualNormCharacterContinuousH1 Order13ActualNormCharacterKummerUnramified
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
open Order13ActualPicardNormContinuousCohomology
open Order13ActualPicardNormAlgebraicKummerInjection
open RepresentationCharacterTwist
open OneDimensionalSelectedQuotientKernel
open Order13ActualOrderedCharacterContinuousH1
open Order13ActualSelectedCharacterExactSequences
open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerKernelControl
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormSubgroupRestrictionF19
open Order13ActualSelectedCharacterKummerKernel
open Order13ActualCharacterKernelLiftsAwayThirteenNineteen
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFactPrimeOfNatNat_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instIsFiniteLeftSchemeSchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instIsFiniteLeftSchemeSchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFactForallEqSubtypePointsMemSubgroupKernelSchemePiHPowOfNat_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFactForallEqSubtypePointsMemSubgroupKernelSchemePiConjugateHPowOfNat_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernelSchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFactNeRatOfNat_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFiniteSubtypePointsMemSubgroupKernelSchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFiniteSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instTopologicalSpacePoints_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instDiscreteTopologyPoints_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instMulActionAlgEquivRatPoints_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernelSchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFiniteDimensionalZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatContinuousH1SchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatContinuousH1SchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernelSchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatH1AlgEquivRatCoefficientPiLineRepresentation_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatH1AlgEquivRatCoefficientTrivialLineRepresentation_order13ActualSelectedCharacterUnramifiedKernelLifts
namespace MazurTransfer.SelectedUnramifiedCharacterKernelLiftProofBoundary20261019
end MazurTransfer.SelectedUnramifiedCharacterKernelLiftProofBoundary20261019
namespace MazurTransfer.SelectedUnramifiedKernelPublicBridges20261019
attribute [local instance] MazurTransfer.Order13ActualNormKernelF19Representation.actualNormKernelF19RepresentationDataV2Provider720261018
theorem normQuotient_kernel_lifts_to_unramifiedClassesAwayThirteenNineteen (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] {U V : Type} [AddCommGroup U] [Module (ZMod 19) U] [AddCommGroup V] [Module (ZMod 19) V] (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U) (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V) (i : Representation.IntertwiningMap σ (kernelRepresentation K φ)) (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ) (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (hsurj : Function.Surjective (normHom K φ))
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap)
    (x : NormQuotient φ) (hx : normQuotientCharacterHom K φ τ p hsurj x = 1) :
    ∃ y ∈ unramifiedClassesAwayThirteenNineteen K σ,
      inclusionClass K φ σ i y = (continuousQuotientHom K φ hsurj x).toAdd :=
  MazurTransfer.order13_character_kernel_lifts_unramified_away_thirteen_nineteen.2.2.1 K φ σ τ i p hφ hsurj hi hp hk x hx
theorem piKummerHom_eq_one_iff_character_lift (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (x : NormQuotient schemePi) :
    piKummerHom K z hz 𝒱 x = 1 ↔ ∃ y : ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient (piLineRepresentation K z hz)),
      piInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePi (schemePi_geometricPoint_surjective K) x).toAdd :=
  MazurTransfer.order13_actual_selected_character_kummer_kernel_certificates.2.2.1 K z hz 𝒱 x
theorem piConjugateKummerHom_eq_one_iff_character_lift (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) (x : NormQuotient schemePiConjugate) :
    piConjugateKummerHom K z hz 𝒱 x = 1 ↔ ∃ y : ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient (trivialLineRepresentation K)),
      piConjugateInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePiConjugate (schemePiConjugate_geometricPoint_surjective K) x).toAdd :=
  MazurTransfer.order13_actual_selected_character_kummer_kernel_certificates.2.2.2 K z hz 𝒱 x
end MazurTransfer.SelectedUnramifiedKernelPublicBridges20261019

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: zero under either ORIGINAL selected character Kummer
map is equivalent to an original character inclusion lift UNRAMIFIED at
EVERY valuation inertia away from thirteen and nineteen, including TWO.
All selected quotient maps and exact coefficient labels remain fixed.
Named downstream consumer: finite-dimensional arithmetic character class
bounds controlling the kernels of actual norm-character pushforward.
-/

noncomputable section
namespace MazurTransfer.SelectedUnramifiedCharacterKernelLiftProof20261019
open Order13ActualSelectedCharacterUnramifiedKernelLifts
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
open Order13ActualNormKernelF19Representation Order13ActualNormFixedKernelEquivalence
open Order13ActualNormKernelFiniteModule
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFactPrimeOfNatNat_order13ActualSelectedCharacterUnramifiedKernelLifts

open Order13ActualPicardSchemeNineteenNorm Order13ActualNormKernelFiniteModule
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instIsFiniteLeftSchemeSchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instIsFiniteLeftSchemeSchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFactForallEqSubtypePointsMemSubgroupKernelSchemePiHPowOfNat_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFactForallEqSubtypePointsMemSubgroupKernelSchemePiConjugateHPowOfNat_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernelSchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatAdditiveSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFactNeRatOfNat_order13ActualSelectedCharacterUnramifiedKernelLifts


attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFiniteSubtypePointsMemSubgroupKernelSchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFiniteSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts


variable [IsAlgClosed K]
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelCrossPairing
open NineteenRootsGaloisRepresentation Order13ActualNineteenTorsionNormPairingAdjoint
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_order13ActualSelectedCharacterUnramifiedKernelLifts


open Order13ActualNormKernelInvariantDimensions Order13ActualComplementaryCharacterExactSequence
open Order13ActualArithmeticCharacterExactSequence Order13ActualCyclotomicThirteenKernelCharacter

open Order13ActualNormCharacterContinuousH1 Order13ActualNormCharacterKummerUnramified
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
open Order13ActualPicardNormContinuousCohomology
open Order13ActualPicardNormAlgebraicKummerInjection
open RepresentationCharacterTwist
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instTopologicalSpacePoints_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instDiscreteTopologyPoints_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instMulActionAlgEquivRatPoints_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernelSchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts
open OneDimensionalSelectedQuotientKernel
open Order13ActualOrderedCharacterContinuousH1
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instFiniteDimensionalZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_order13ActualSelectedCharacterUnramifiedKernelLifts

variable (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)

open Order13ActualSelectedCharacterExactSequences
open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerKernelControl
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormSubgroupRestrictionF19
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatContinuousH1SchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatContinuousH1SchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernelSchemePi_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernelSchemePiConjugate_order13ActualSelectedCharacterUnramifiedKernelLifts

open Order13ActualSelectedCharacterKummerKernel
open Order13ActualCharacterKernelLiftsAwayThirteenNineteen
local notation "Γ" => K ≃ₐ[ℚ] K
local notation "Hχ" => ContinuousFirstCohomologyPresentation.H1 Γ (Coefficient (piLineRepresentation K z hz))
local notation "H₀" => ContinuousFirstCohomologyPresentation.H1 Γ (Coefficient (trivialLineRepresentation K))
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatH1AlgEquivRatCoefficientPiLineRepresentation_order13ActualSelectedCharacterUnramifiedKernelLifts
attribute [local instance] MazurTransfer.Order13ActualSelectedCharacterUnramifiedKernelLifts.instModuleZModOfNatNatH1AlgEquivRatCoefficientTrivialLineRepresentation_order13ActualSelectedCharacterUnramifiedKernelLifts





theorem piKummer_kernel_lifts_to_unramified_classes
    (x : NormQuotient schemePi) (hx : piKummerHom K z hz 𝒱 x = 1) :
    ∃ y ∈ piUnramifiedCharacterClasses K z hz,
      piInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePi (schemePi_geometricPoint_surjective K) x).toAdd :=
  MazurTransfer.SelectedUnramifiedKernelPublicBridges20261019.normQuotient_kernel_lifts_to_unramifiedClassesAwayThirteenNineteen K schemePi
    (piLineRepresentation K z hz) (rootsRepresentation K)
    (selectedPiInclusion K z hz 𝒱) (piQuotient K z hz 𝒱) (Or.inl rfl)
    (schemePi_geometricPoint_surjective K) (selectedPiInclusion_injective K z hz 𝒱)
    (piQuotient_surjective K z hz 𝒱) (selectedPiInclusion_range K z hz 𝒱) x hx

theorem piConjugateKummer_kernel_lifts_to_unramified_classes
    (x : NormQuotient schemePiConjugate) (hx : piConjugateKummerHom K z hz 𝒱 x = 1) :
    ∃ y ∈ piConjugateUnramifiedCharacterClasses K,
      piConjugateInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePiConjugate (schemePiConjugate_geometricPoint_surjective K) x).toAdd :=
  MazurTransfer.SelectedUnramifiedKernelPublicBridges20261019.normQuotient_kernel_lifts_to_unramifiedClassesAwayThirteenNineteen K schemePiConjugate
    (trivialLineRepresentation K) (twistedRootsRepresentation K z hz)
    (selectedPiConjugateInclusion K z hz 𝒱) (piConjugateQuotient K z hz 𝒱) (Or.inr rfl)
    (schemePiConjugate_geometricPoint_surjective K) (selectedPiConjugateInclusion_injective K z hz 𝒱)
    (piConjugateQuotient_surjective K z hz 𝒱) (selectedPiConjugateInclusion_range K z hz 𝒱) x hx

theorem piKummer_eq_one_iff_unramified_character_lift (x : NormQuotient schemePi) :
    piKummerHom K z hz 𝒱 x = 1 ↔ ∃ y ∈ piUnramifiedCharacterClasses K z hz,
      piInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePi (schemePi_geometricPoint_surjective K) x).toAdd := by
  constructor
  · exact piKummer_kernel_lifts_to_unramified_classes K z hz 𝒱 x
  · rintro ⟨y, -, hy⟩
    exact (MazurTransfer.SelectedUnramifiedKernelPublicBridges20261019.piKummerHom_eq_one_iff_character_lift K z hz 𝒱 x).mpr ⟨y, hy⟩

theorem piConjugateKummer_eq_one_iff_unramified_character_lift (x : NormQuotient schemePiConjugate) :
    piConjugateKummerHom K z hz 𝒱 x = 1 ↔ ∃ y ∈ piConjugateUnramifiedCharacterClasses K,
      piConjugateInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePiConjugate (schemePiConjugate_geometricPoint_surjective K) x).toAdd := by
  constructor
  · exact piConjugateKummer_kernel_lifts_to_unramified_classes K z hz 𝒱 x
  · rintro ⟨y, -, hy⟩
    exact (MazurTransfer.SelectedUnramifiedKernelPublicBridges20261019.piConjugateKummerHom_eq_one_iff_character_lift K z hz 𝒱 x).mpr ⟨y, hy⟩

end MazurTransfer.SelectedUnramifiedCharacterKernelLiftProof20261019

end
theorem solution : (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover), ∀ (x : NormQuotient schemePi) (hx : piKummerHom K z hz 𝒱 x = 1), ∃ y ∈ piUnramifiedCharacterClasses K z hz,
      piInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePi (schemePi_geometricPoint_surjective K) x).toAdd) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover), ∀ (x : NormQuotient schemePiConjugate) (hx : piConjugateKummerHom K z hz 𝒱 x = 1), ∃ y ∈ piConjugateUnramifiedCharacterClasses K,
      piConjugateInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePiConjugate (schemePiConjugate_geometricPoint_surjective K) x).toAdd) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover), ∀ (x : NormQuotient schemePi), piKummerHom K z hz 𝒱 x = 1 ↔ ∃ y ∈ piUnramifiedCharacterClasses K z hz,
      piInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePi (schemePi_geometricPoint_surjective K) x).toAdd) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (z : K) (hz : IsPrimitiveRoot z 13) (𝒱 : (curveScheme ℚ).TwoAffineOpenCover), ∀ (x : NormQuotient schemePiConjugate), piConjugateKummerHom K z hz 𝒱 x = 1 ↔ ∃ y ∈ piConjugateUnramifiedCharacterClasses K,
      piConjugateInclusionClass K z hz 𝒱 y =
        (continuousQuotientHom K schemePiConjugate (schemePiConjugate_geometricPoint_surjective K) x).toAdd) := by
  exact ⟨MazurTransfer.SelectedUnramifiedCharacterKernelLiftProof20261019.piKummer_kernel_lifts_to_unramified_classes, MazurTransfer.SelectedUnramifiedCharacterKernelLiftProof20261019.piConjugateKummer_kernel_lifts_to_unramified_classes, MazurTransfer.SelectedUnramifiedCharacterKernelLiftProof20261019.piKummer_eq_one_iff_unramified_character_lift, MazurTransfer.SelectedUnramifiedCharacterKernelLiftProof20261019.piConjugateKummer_eq_one_iff_unramified_character_lift⟩
#print axioms solution
