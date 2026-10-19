-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_norm_group_laws_and_composition
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T10:01:31.313097+00:00
-- url     : https://prove2.me/submissions/bcd7a367-e8cd-46fc-aeb2-20caa54175f4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same original generic and integral group laws, transported norm multiplication, all compositions and identities, and both actual scalar-nineteen composites.
Named downstream consumer: comparison with relative scalar nineteen, finite etale fibres and inertia at two.
-/
import Definitions.Def_MazurTransfer_Order13DyadicOriginalIntegralNormGroupLawAndCompositionData20261019
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalChosenPicardNeronModelData20261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedRationalPicardComparison Order13DyadicMixedPicardGeometry
open Order13DyadicMixedGenericNorms Order13DyadicMixedIntegralNormExtensions
open Order13DyadicMixedGenericGroupIdentity Order13DyadicMixedGenericNormGroupLaws
open Order13DyadicMixedIntegralNormGroupLaws Order13DyadicMixedIntegralNormComposition
open scoped CategoryTheory.MonObj
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
attribute [local instance] MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.originalDyadicChosenPicardNeronPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormGroupLaws.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormGroupLaws
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNormUnit.instGrpObjOverSchemeSpecOfRatMkToBaseRationalPicard_order13DyadicMixedGenericNormUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNormUnit.instFactPrimeOfNatNat_order13DyadicMixedGenericNormUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericGroupIdentity.instFactPrimeOfNatNat_order13DyadicMixedGenericGroupIdentity
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNormGroupLaws.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedGenericNormGroupLaws
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormComposition.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormComposition
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormPointwiseUnit.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormPointwiseUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormPointwiseUnit.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormPointwiseUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNormUnit.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedGenericNormUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNormGroupLaws.instFactPrimeOfNatNat_order13DyadicMixedGenericNormGroupLaws
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormUnit.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormUnit.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormUnit
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormGroupLaws.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormGroupLaws
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormComposition.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13DyadicMixedIntegralNormComposition
namespace MazurTransfer.ActualDyadicOriginalNormGroupCompositionProofBoundary20261019
end MazurTransfer.ActualDyadicOriginalNormGroupCompositionProofBoundary20261019
theorem solution : (∀ {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ))
    (x y : SchemeHomOver t (rationalPicard).toBase), (genericLocalLaw).mul t x y = (genericRepresentedLaw).mul t x y) ∧ (∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of ℚ))
    (x y : SchemeHomOver t (rationalPicard).toBase), NeronModelInfra.schemeHomOverComp ((genericLocalLaw).mul t x y)
      (genericNorm φ) =
    (genericLocalLaw).mul t
      (NeronModelInfra.schemeHomOverComp x (genericNorm φ))
      (NeronModelInfra.schemeHomOverComp y (genericNorm φ))) ∧ (∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], NeronModelInfra.schemeHomOverComp ((dyadicLaw).one (𝟙 _))
      (integralNorm φ) = (dyadicLaw).one (𝟙 _)) ∧ (∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    {T : Scheme} (t : T ⟶ Spec (CommRingCat.of (BaseRing)))
    (x y : SchemeHomOver t (dyadicPicard).toBase), NeronModelInfra.schemeHomOverComp ((dyadicLaw).mul t x y) (integralNorm φ) =
    (dyadicLaw).mul t
      (NeronModelInfra.schemeHomOverComp x (integralNorm φ))
      (NeronModelInfra.schemeHomOverComp y (integralNorm φ))) ∧ (∀ (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase), integralNorm (φ ≫ ψ) =
      schemeHomOverComp (integralNorm φ) (integralNorm ψ)) ∧ (integralNorm (𝟙 (Over.mk actualPicard.toBase)) =
      schemeHomOverId (dyadicPicard).toBase) ∧ (schemeHomOverComp (integralPi) (integralPiConjugate) =
      integralScalarNineteen) ∧ (schemeHomOverComp (integralPiConjugate) (integralPi) =
      integralScalarNineteen) ∧ (schemeHomOverComp (integralPi) (integralPiConjugate) =
      schemeHomOverComp (integralPiConjugate) (integralPi)) := by
  exact ⟨MazurTransfer.Order13DyadicMixedGenericNormGroupLaws.generic_group_law_multiplications_equal, MazurTransfer.Order13DyadicMixedGenericNormGroupLaws.localGenericNorm_preserves_mul, MazurTransfer.Order13DyadicMixedIntegralNormUnit.integralNorm_preserves_unit, MazurTransfer.Order13DyadicMixedIntegralNormGroupLaws.integralNorm_preserves_mul, MazurTransfer.Order13DyadicMixedIntegralNormComposition.integralNorm_comp, MazurTransfer.Order13DyadicMixedIntegralNormComposition.integralNorm_id, MazurTransfer.Order13DyadicMixedIntegralNormComposition.integralPi_comp_integralPiConjugate, MazurTransfer.Order13DyadicMixedIntegralNormComposition.integralPiConjugate_comp_integralPi, MazurTransfer.Order13DyadicMixedIntegralNormComposition.integralNorms_commute⟩
#print axioms solution
