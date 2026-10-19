-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_continuous_norm_kummer_and_fixed_quotient_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T11:21:42.438391+00:00
-- url     : https://prove2.me/submissions/b2e4bed8-b351-4c65-820e-315b35d7f74e

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual continuous norm Kummer classes, including both fixed norm quotient injections, restrict to zero on EVERY genuine valuation inertia subgroup above TWO.
Named downstream consumer: all-prime selected character unramified kernel conditions, actual norm Selmer dimensions and rank zero.
-/
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalFixedNormQuotientScopedProvidersData20261019
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_internal_norm_morphisms_and_inertia
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormSubgroupRestriction_restrictedClass_zero_iff_subgroup_invariant_preimage
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricNormPreimages_schemePi_geometricPoint_surjective
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricNormPreimages_schemePiConjugate_geometricPoint_surjective
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormAlgebraicKummerInjection Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormContinuousCohomology
open Order13LocalIntegralCoefficientMaps
open Order13DyadicMixedQuadraticCharts
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsGaloisRatAlgebraicClosure_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsFiniteLeftSchemeSchemePiConjugate_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsFiniteLeftSchemeSchemePi_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instTopologicalSpacePoints_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instMulActionAlgEquivRatPoints_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instFactPrimeOfNatNat_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instDiscreteTopologyPoints_order13DyadicMixedUnramifiedKummer
namespace MazurTransfer.ActualDyadicContinuousKummerTheoremProofBoundary20261019
end MazurTransfer.ActualDyadicContinuousKummerTheoremProofBoundary20261019
namespace MazurTransfer.DyadicKummerPublicInertiaBridge20261019
theorem actual_norm_lift_of_rational_point_inertia_fixed {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra BaseRing Ω] [IsScalarTower BaseRing ℚ Ω]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring Ω) (hA : A.LiesOverPrime 2)
    (σ : Ω ≃ₐ[ℚ] Ω) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω))) actualPicard.toBase)
    (p : Spec (CommRingCat.of ℚ) ⟶ actualPicard.P)
    (hx : x.val ≫ φ.left = Spec.map (CommRingCat.ofHom (algebraMap ℚ Ω)) ≫ p) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.val = x.val :=
  MazurTransfer.order13_actual_dyadic_internal_norm_morphisms_and_inertia.2.2.2 (Ω := Ω) φ hφ A hA σ hσ x p hx
end MazurTransfer.DyadicKummerPublicInertiaBridge20261019

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous Kummer classes for the SAME actual rational
norm maps restrict to zero on the genuine valuation inertia groups at
the prime TWO, via the actual mixed dyadic Picard model.
The original good-prime proof specializes to the now proved actual
dyadic norm inertia theorem. No assumptions on 104-invertibility enter.
Named downstream consumer: global norm Selmer bounds.
-/

noncomputable section
namespace MazurTransfer.DyadicContinuousKummerTheoremBody20261019.Order13DyadicMixedUnramifiedKummer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13LocalIntegralCoefficientMaps
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedUnramifiedKummer

attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instFactPrimeOfNatNat_order13DyadicMixedUnramifiedKummer
variable (K : Type) [Field K] [CharZero K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]

theorem norm_lift_inertia_fixed (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime 2)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    actionHom K σ b = b := by
  letI : Algebra (LocalRing 2) K :=
    ((algebraMap ℚ K).comp (algebraMap (LocalRing 2) ℚ)).toAlgebra
  letI : IsScalarTower (LocalRing 2) ℚ K :=
    IsScalarTower.of_algebraMap_eq' (R := LocalRing 2) (S := ℚ) (A := K) rfl
  have hb' : b.left ≫ φ.left =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ K)) ≫ a.left :=
    congrArg (fun z => z.left) hb
  have h := MazurTransfer.DyadicKummerPublicInertiaBridge20261019.actual_norm_lift_of_rational_point_inertia_fixed
    φ hφ A hA σ hσ ⟨b.left, b.w⟩ a.left hb'
  apply Over.OverMorphism.ext
  exact h

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable [IsGalois ℚ K]

attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instTopologicalSpacePoints_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instDiscreteTopologyPoints_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instMulActionAlgEquivRatPoints_order13DyadicMixedUnramifiedKummer
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instMulDistribMulActionAlgEquivRatSubtypePointsMemSubgroupKernel_order13DyadicMixedUnramifiedKummer
open Order13ActualPicardNormAlgebraicCohomology Order13ActualPicardNormContinuousCocycles
variable [IsFinite φ.left]
attribute [local instance] MazurTransfer.Order13DyadicMixedUnramifiedKummer.instContinuousSMulAlgEquivRatSubtypePointsMemSubgroupKernel_order13DyadicMixedUnramifiedKummer
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormSubgroupRestriction

theorem continuous_norm_class_unramified
    (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime 2)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    restrictNormClass K φ (A.inertiaSubgroupIn ℚ)
      (continuousClassOfLift K φ a b hb) = 0 := by
  apply (restrictedClass_zero_iff_subgroup_invariant_preimage K φ
    (A.inertiaSubgroupIn ℚ) a b hb).mpr
  exact ⟨b, hb, fun σ => norm_lift_inertia_fixed K φ hφ A hA a b hb σ.val σ.property⟩

end MazurTransfer.DyadicContinuousKummerTheoremBody20261019.Order13DyadicMixedUnramifiedKummer

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two FIXED actual continuous Kummer injections from
the rational norm quotients have zero restriction to every genuine
valuation inertia subgroup above TWO. All geometric lift existence and
finiteness inputs are proved for the actual maps.
Named downstream consumer: actual norm Selmer conditions at thirteen
and nineteen, followed by the rational rank bound.
-/

noncomputable section
namespace MazurTransfer.DyadicContinuousKummerTheoremBody20261019.Order13ActualDyadicNormQuotientKummerCondition
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormContinuousCohomology
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsMonHomOverSchemeSpecOfRatSchemePi_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsMonHomOverSchemeSpecOfRatSchemePiConjugate_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsFiniteLeftSchemeSchemePi_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsFiniteLeftSchemeSchemePiConjugate_order13ActualDyadicNormQuotientKummerCondition
attribute [local instance] MazurTransfer.Order13ActualDyadicNormQuotientKummerCondition.instIsGaloisRatAlgebraicClosure_order13ActualDyadicNormQuotientKummerCondition

theorem actualPiKummer_dyadic_unramified
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2)
    (x : NormQuotient schemePi) :
    restrictNormClass (AlgebraicClosure ℚ) schemePi (A.inertiaSubgroupIn ℚ)
      (actualPiAlgebraicClosureContinuousKummerGroupHom x).toAdd = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  exact DyadicContinuousKummerTheoremBody20261019.Order13DyadicMixedUnramifiedKummer.continuous_norm_class_unramified
    (AlgebraicClosure ℚ) schemePi (Or.inl rfl) A hA a
    (chosenLift (AlgebraicClosure ℚ) schemePi
      (schemePi_geometricPoint_surjective (AlgebraicClosure ℚ)) a)
    (chosenLift_spec (AlgebraicClosure ℚ) schemePi
      (schemePi_geometricPoint_surjective (AlgebraicClosure ℚ)) a)

theorem actualPiConjugateKummer_dyadic_unramified
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2)
    (x : NormQuotient schemePiConjugate) :
    restrictNormClass (AlgebraicClosure ℚ) schemePiConjugate (A.inertiaSubgroupIn ℚ)
      (actualPiConjugateAlgebraicClosureContinuousKummerGroupHom x).toAdd = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  exact DyadicContinuousKummerTheoremBody20261019.Order13DyadicMixedUnramifiedKummer.continuous_norm_class_unramified
    (AlgebraicClosure ℚ) schemePiConjugate (Or.inr rfl) A hA a
    (chosenLift (AlgebraicClosure ℚ) schemePiConjugate
      (schemePiConjugate_geometricPoint_surjective (AlgebraicClosure ℚ)) a)
    (chosenLift_spec (AlgebraicClosure ℚ) schemePiConjugate
      (schemePiConjugate_geometricPoint_surjective (AlgebraicClosure ℚ)) a)

end MazurTransfer.DyadicContinuousKummerTheoremBody20261019.Order13ActualDyadicNormQuotientKummerCondition

end

theorem solution : (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime 2)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a)
    (σ : K ≃ₐ[ℚ] K) (hσ : σ ∈ A.inertiaSubgroupIn ℚ), actionHom K σ b = b) ∧ (∀ (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsGalois ℚ K] [IsFinite φ.left], ∀ (hφ : φ = schemePi ∨ φ = schemePiConjugate)
    (A : ValuationSubring K) (hA : A.LiesOverPrime 2)
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a), restrictNormClass K φ (A.inertiaSubgroupIn ℚ)
      (continuousClassOfLift K φ a b hb) = 0) ∧ (∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2)
    (x : NormQuotient schemePi), restrictNormClass (AlgebraicClosure ℚ) schemePi (A.inertiaSubgroupIn ℚ)
      (actualPiAlgebraicClosureContinuousKummerGroupHom x).toAdd = 0) ∧ (∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2)
    (x : NormQuotient schemePiConjugate), restrictNormClass (AlgebraicClosure ℚ) schemePiConjugate (A.inertiaSubgroupIn ℚ)
      (actualPiConjugateAlgebraicClosureContinuousKummerGroupHom x).toAdd = 0) := by
  exact ⟨MazurTransfer.DyadicContinuousKummerTheoremBody20261019.Order13DyadicMixedUnramifiedKummer.norm_lift_inertia_fixed, MazurTransfer.DyadicContinuousKummerTheoremBody20261019.Order13DyadicMixedUnramifiedKummer.continuous_norm_class_unramified, MazurTransfer.DyadicContinuousKummerTheoremBody20261019.Order13ActualDyadicNormQuotientKummerCondition.actualPiKummer_dyadic_unramified, MazurTransfer.DyadicContinuousKummerTheoremBody20261019.Order13ActualDyadicNormQuotientKummerCondition.actualPiConjugateKummer_dyadic_unramified⟩
#print axioms solution
