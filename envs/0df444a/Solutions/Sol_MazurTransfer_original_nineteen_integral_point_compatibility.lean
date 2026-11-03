-- Prove2me | solution 1 for MazurTransfer.original_nineteen_integral_point_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-11-02T17:31:00.711464+00:00
-- url     : https://prove2.me/submissions/7fb7b48c-a0b0-4fc2-ac89-5271fa2a781a

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the unique integral extension of the same actual rational Picard point agrees with the previously fixed arithmetic field comparison over every compatible characteristic-zero field.
Named downstream consumer: both actual norm-preimage torsors and the original selected character Kummer cocycle.
-/
import Definitions.Def_MazurTransfer_OriginalNineteenIntegralPointCompatibilityData20261020
import Theorems.Thm_MazurTransfer_original_exceptional_nineteen_norm_model_properties
import Theorems.Thm_MazurTransfer_original_integral_arithmetic_field_point_comparison_laws
noncomputable section
open MazurTransfer

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13ExceptionalNineteenFlatNormFibres Order13LocalIntegralCoefficientMaps
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeLocalGenericPicardComparison
open Order13IntegralGenericPointComparison Order13IntegralArithmeticFieldPointComparison
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricNormPreimages
open RelativeNormPreimageRepresentation Order13ActualIntegralNormPreimageTorsors
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13NineteenIntegralPointCompatibility
local notation "R" => LocalRing 19
attribute [local instance] MazurTransfer.Order13NineteenIntegralPointCompatibility.instFactPrimeOfNatNat_order13NineteenIntegralPointCompatibility
attribute [local instance] MazurTransfer.Order13NineteenIntegralPointCompatibility.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13NineteenIntegralPointCompatibility
namespace MazurTransfer.OriginalNineteenIntegralPointCompatibilityBoundary20261020
end MazurTransfer.OriginalNineteenIntegralPointCompatibilityBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the UNIQUE integral extension of the SAME actual rational
Picard point agrees with the PREVIOUSLY FIXED arithmetic field comparison
at every compatible characteristic-zero field. Both norm torsors use it.
Named downstream consumer: identification of the actual norm-preimage
torsor's field points and its original selected character Kummer cocycle.
-/

noncomputable section
namespace MazurTransfer.OriginalNineteenIntegralPointCompatibilityProof20261020
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13ExceptionalNineteenFlatNormFibres Order13LocalIntegralCoefficientMaps
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeLocalGenericPicardComparison
open Order13IntegralGenericPointComparison Order13IntegralArithmeticFieldPointComparison
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricNormPreimages
open RelativeNormPreimageRepresentation Order13ActualIntegralNormPreimageTorsors
open scoped CategoryTheory.MonObj



variable (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase)



theorem integralPoint_restrict :
    genericFibreRestrict R ℚ integralModel.toBase (𝟙 (Spec (CommRingCat.of R))) (integralPoint a) =
      actualGenericPoint a :=
  (MazurTransfer.original_exceptional_nineteen_norm_model_properties.2.1 a).choose_spec.1

theorem integralPoint_unique (b : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) integralModel.toBase)
    (hb : genericFibreRestrict R ℚ integralModel.toBase (𝟙 (Spec (CommRingCat.of R))) b =
      actualGenericPoint a) : b = integralPoint a :=
  (MazurTransfer.original_exceptional_nineteen_norm_model_properties.2.1 a).choose_spec.2 b hb

theorem integralPoint_generic_projection :
    localGenericInclusion 19 ≫ (integralPoint a).val =
      (a.val ≫ (actualLocalGenericOverIso 19 nineteen_good).hom.left) ≫
        pullback.fst integralModel.toBase (localGenericInclusion 19) := by
  let p := genericBaseToRationals
  letI : IsIso p := by dsimp [p, genericBaseToRationals, genericBase]; infer_instance
  apply (cancel_epi p).mp
  have h := congrArg (fun x : SchemeHomOver genericBaseToRationals
      (localGenericPicard 19 nineteen_good).toBase =>
        x.val ≫ pullback.fst integralModel.toBase (localGenericInclusion 19)) (integralPoint_restrict a)
  change (pullback.lift
      (pullback.fst (𝟙 (Spec (CommRingCat.of R))) (localGenericInclusion 19) ≫ (integralPoint a).val)
      p _) ≫ pullback.fst integralModel.toBase (localGenericInclusion 19) =
    (p ≫ a.val ≫ (actualLocalGenericOverIso 19 nineteen_good).hom.left) ≫
      pullback.fst integralModel.toBase (localGenericInclusion 19) at h
  rw [pullback.lift_fst] at h
  have hb : pullback.fst (𝟙 (Spec (CommRingCat.of R))) (localGenericInclusion 19) =
      p ≫ localGenericInclusion 19 := by
    simpa only [Category.comp_id] using
      (pullback.condition (f := 𝟙 (Spec (CommRingCat.of R))) (g := localGenericInclusion 19))
  rw [hb] at h
  exact ((Category.assoc p (localGenericInclusion 19) (integralPoint a).val).symm.trans h).trans
    (Category.assoc p (a.val ≫ (actualLocalGenericOverIso 19 nineteen_good).hom.left)
      (pullback.fst integralModel.toBase (localGenericInclusion 19)))

variable (K : Type) [Field K] [CharZero K]
variable [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K]



theorem integralPoint_field_compatibility (b : RationalPoints) :
    fixedActualFieldPointEquiv K (rationalPoint K b) =
      pulledPoint (integralPoint (overHomToSchemeHomOver b))
        (FieldAutomorphismOverPointAction.fieldBase R K) := by
  apply Subtype.ext
  change ((FieldAutomorphismOverPointAction.fieldBase ℚ K ≫ b.left) ≫
      (actualLocalGenericOverIso 19 nineteen_good).hom.left) ≫
        pullback.fst integralModel.toBase (localGenericInclusion 19) =
    FieldAutomorphismOverPointAction.fieldBase R K ≫ (integralPoint (overHomToSchemeHomOver b)).val
  calc
    _ = FieldAutomorphismOverPointAction.fieldBase ℚ K ≫
        ((b.left ≫ (actualLocalGenericOverIso 19 nineteen_good).hom.left) ≫
          pullback.fst integralModel.toBase (localGenericInclusion 19)) := by
      exact (congrArg (fun z => z ≫ pullback.fst integralModel.toBase (localGenericInclusion 19))
        (Category.assoc (FieldAutomorphismOverPointAction.fieldBase ℚ K) b.left
          (actualLocalGenericOverIso 19 nineteen_good).hom.left)).trans
        (Category.assoc (FieldAutomorphismOverPointAction.fieldBase ℚ K)
          (b.left ≫ (actualLocalGenericOverIso 19 nineteen_good).hom.left)
          (pullback.fst integralModel.toBase (localGenericInclusion 19)))
    _ = FieldAutomorphismOverPointAction.fieldBase ℚ K ≫
        (localGenericInclusion 19 ≫ (integralPoint (overHomToSchemeHomOver b)).val) :=
      congrArg (fun z => FieldAutomorphismOverPointAction.fieldBase ℚ K ≫ z)
        (integralPoint_generic_projection (overHomToSchemeHomOver b)).symm
    _ = (FieldAutomorphismOverPointAction.fieldBase ℚ K ≫ localGenericInclusion 19) ≫
        (integralPoint (overHomToSchemeHomOver b)).val := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun z => z ≫ (integralPoint (overHomToSchemeHomOver b)).val)
      (MazurTransfer.original_integral_arithmetic_field_point_comparison_laws.1 19 K)

end MazurTransfer.OriginalNineteenIntegralPointCompatibilityProof20261020

theorem solution : (∀ (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase), genericFibreRestrict R ℚ integralModel.toBase (𝟙 (Spec (CommRingCat.of R))) (integralPoint a) =
      actualGenericPoint a) ∧ (∀ (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase), ∀ (b : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) integralModel.toBase)
    (hb : genericFibreRestrict R ℚ integralModel.toBase (𝟙 (Spec (CommRingCat.of R))) b =
      actualGenericPoint a),
b = integralPoint a) ∧ (∀ (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase), localGenericInclusion 19 ≫ (integralPoint a).val =
      (a.val ≫ (actualLocalGenericOverIso 19 nineteen_good).hom.left) ≫
        pullback.fst integralModel.toBase (localGenericInclusion 19)) ∧ (∀ (K : Type) [Field K] [CharZero K] [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K], ∀ (b : RationalPoints),
fixedActualFieldPointEquiv K (rationalPoint K b) =
      pulledPoint (integralPoint (overHomToSchemeHomOver b))
        (FieldAutomorphismOverPointAction.fieldBase R K)) := by
  exact ⟨MazurTransfer.OriginalNineteenIntegralPointCompatibilityProof20261020.integralPoint_restrict, MazurTransfer.OriginalNineteenIntegralPointCompatibilityProof20261020.integralPoint_unique, MazurTransfer.OriginalNineteenIntegralPointCompatibilityProof20261020.integralPoint_generic_projection, MazurTransfer.OriginalNineteenIntegralPointCompatibilityProof20261020.integralPoint_field_compatibility⟩
#print axioms solution
