-- Prove2me | solution 1 for MazurTransfer.original_integral_arithmetic_field_point_comparison_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T03:03:24.622672+00:00
-- url     : https://prove2.me/submissions/ce691141-7301-4963-9d8f-c07e117fdfb9

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same canonical integral/generic Picard comparison on arithmetic field points preserves its original group operations, every chosen integral endomorphism extension and spectrum-precomposition Galois action.
Named downstream consumer: the same actual integral norm-kernel Hopf arithmetic point labels.
-/
import Definitions.Def_MazurTransfer_OriginalIntegralArithmeticFieldPointComparisonData20261020
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralNormExtensionsData
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerData
import Theorems.Thm_MazurTransfer_original_integral_generic_point_comparison_laws
import Theorems.Thm_MazurTransfer_original_relative_point_base_cast_laws
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTransfer.Order13IntegralGenericPointComparison MazurTransfer.RelativePointBaseCast
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13GoodPrimeLocalPicardModels
open MazurTransfer.Order13GoodPrimeIntegralNormExtensions MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13SameIntegralPicardRationalSchemeComparison MazurTransfer.Order13ActualPicardGeometricNormPreimages
open MazurTransfer.Order13ActualPicardNormKummerCocycles MazurTransfer.Order13IntegralArithmeticFieldPointComparison
open scoped CategoryTheory.MonObj
attribute [local instance] MazurTransfer.Order13IntegralArithmeticFieldPointComparison.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralArithmeticFieldPointComparison
namespace MazurTransfer.OriginalIntegralArithmeticFieldPointComparisonBoundary20261020
end MazurTransfer.OriginalIntegralArithmeticFieldPointComparisonBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: specialize the SAME canonical local/generic point
comparison to field-valued arithmetic points with the canonical scalar
tower. Preserve actual multiplication, zero, norm maps and the existing
arithmetic Galois action by spectrum precomposition.
Named downstream consumer: actual integral norm-kernel Hopf point labels.
-/

noncomputable section
namespace MazurTransfer.OriginalIntegralArithmeticFieldPointComparisonProof20261020
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13IntegralGenericPointComparison RelativePointBaseCast
open Order13LocalIntegralCoefficientMaps Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
variable (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104)
variable (K : Type) [Field K] [CharZero K]
variable [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K]


theorem fieldBase_comp :
    FieldAutomorphismOverPointAction.fieldBase ℚ K ≫ localGenericInclusion q =
      FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℚ K)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (LocalRing q) ℚ)) =
      Spec.map (CommRingCat.ofHom (algebraMap (LocalRing q) K))
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (IsScalarTower.algebraMap_apply (LocalRing q) ℚ K r).symm



theorem actualFieldPointEquiv_one :
    actualFieldPointEquiv q hq K 1 =
      (localLaw q hq).one (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K) := by
  exact (congrArg (pointEquiv (fieldBase_comp q K))
    ((MazurTransfer.original_integral_generic_point_comparison_laws).1 q hq (FieldAutomorphismOverPointAction.fieldBase ℚ K))).trans
      ((MazurTransfer.original_relative_point_base_cast_laws).2.2.2.1 (localLaw q hq) (fieldBase_comp q K))

theorem actualFieldPointEquiv_mul (a b : Points K) :
    actualFieldPointEquiv q hq K (a * b) =
      (localLaw q hq).mul (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)
        (actualFieldPointEquiv q hq K a) (actualFieldPointEquiv q hq K b) := by
  exact (congrArg (pointEquiv (fieldBase_comp q K))
    ((MazurTransfer.original_integral_generic_point_comparison_laws).2.1 q hq (FieldAutomorphismOverPointAction.fieldBase ℚ K) a b)).trans
      ((MazurTransfer.original_relative_point_base_cast_laws).2.2.2.2 (localLaw q hq) (fieldBase_comp q K) _ _)

theorem actualFieldPointEquiv_norm
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) (a : Points K) :
    actualFieldPointEquiv q hq K (a ≫ φ) =
      NeronModelInfra.schemeHomOverComp (actualFieldPointEquiv q hq K a) (integralNorm q hq φ) := by
  exact (congrArg (pointEquiv (fieldBase_comp q K))
    ((MazurTransfer.original_integral_generic_point_comparison_laws).2.2.2.2 q hq (FieldAutomorphismOverPointAction.fieldBase ℚ K) φ a)).trans
      ((MazurTransfer.original_relative_point_base_cast_laws).2.1 (fieldBase_comp q K) (integralNorm q hq φ) _)

theorem fieldAut_over_local (σ : K ≃ₐ[ℚ] K) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K =
        FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K := by
  exact Over.w (FieldAutomorphismOverPointAction.fieldAut (LocalRing q) K
    (σ.restrictScalars (LocalRing q)))

theorem actualFieldPointEquiv_act (σ : K ≃ₐ[ℚ] K) (a : Points K) :
    actualFieldPointEquiv q hq K (actionHom K σ a) =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (fieldAut_over_local q K σ) (actualFieldPointEquiv q hq K a) := by
  let ψ := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have hQ : ψ ≫ FieldAutomorphismOverPointAction.fieldBase ℚ K =
      FieldAutomorphismOverPointAction.fieldBase ℚ K :=
    Over.w (FieldAutomorphismOverPointAction.fieldAut ℚ K σ)
  have h := (MazurTransfer.original_integral_generic_point_comparison_laws).2.2.1 q hq
    (FieldAutomorphismOverPointAction.fieldBase ℚ K)
    (FieldAutomorphismOverPointAction.fieldBase ℚ K) ψ hQ a
  have h' := congrArg (pointEquiv (fieldBase_comp q K)) h
  exact h'.trans ((MazurTransfer.original_relative_point_base_cast_laws).2.2.1 (fieldBase_comp q K) (fieldBase_comp q K)
    ψ (by rw [← Category.assoc, hQ]) (fieldAut_over_local q K σ) (actualToLocal q hq a))

end MazurTransfer.OriginalIntegralArithmeticFieldPointComparisonProof20261020

theorem solution : (∀ (q : ℕ) [Fact q.Prime] (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], FieldAutomorphismOverPointAction.fieldBase ℚ K ≫ localGenericInclusion q =
      FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], actualFieldPointEquiv q hq K 1 =
      (localLaw q hq).one (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], ∀ (a b : Points K),
actualFieldPointEquiv q hq K (a * b) =
      (localLaw q hq).mul (FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K)
        (actualFieldPointEquiv q hq K a) (actualFieldPointEquiv q hq K b)) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], ∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) (a : Points K),
actualFieldPointEquiv q hq K (a ≫ φ) =
      NeronModelInfra.schemeHomOverComp (actualFieldPointEquiv q hq K a) (integralNorm q hq φ)) ∧ (∀ (q : ℕ) [Fact q.Prime] (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], ∀ (σ : K ≃ₐ[ℚ] K),
Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K =
        FieldAutomorphismOverPointAction.fieldBase (LocalRing q) K) ∧ (∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (K : Type) [Field K] [CharZero K] [Algebra (LocalRing q) K] [IsScalarTower (LocalRing q) ℚ K], ∀ (σ : K ≃ₐ[ℚ] K) (a : Points K),
actualFieldPointEquiv q hq K (actionHom K σ a) =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (Over.w (FieldAutomorphismOverPointAction.fieldAut (LocalRing q) K (σ.restrictScalars (LocalRing q)))) (actualFieldPointEquiv q hq K a)) := by
  exact ⟨MazurTransfer.OriginalIntegralArithmeticFieldPointComparisonProof20261020.fieldBase_comp, MazurTransfer.OriginalIntegralArithmeticFieldPointComparisonProof20261020.actualFieldPointEquiv_one, MazurTransfer.OriginalIntegralArithmeticFieldPointComparisonProof20261020.actualFieldPointEquiv_mul, MazurTransfer.OriginalIntegralArithmeticFieldPointComparisonProof20261020.actualFieldPointEquiv_norm, MazurTransfer.OriginalIntegralArithmeticFieldPointComparisonProof20261020.fieldAut_over_local, MazurTransfer.OriginalIntegralArithmeticFieldPointComparisonProof20261020.actualFieldPointEquiv_act⟩
#print axioms solution
