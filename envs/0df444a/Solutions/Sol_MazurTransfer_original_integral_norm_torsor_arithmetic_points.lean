-- Prove2me | solution 1 for MazurTransfer.original_integral_norm_torsor_arithmetic_points
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-11-02T17:54:27.038764+00:00
-- url     : https://prove2.me/submissions/5280fd54-e9ad-4042-a891-a8fce5dde590

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the same integral norm torsor field points with the previously fixed rational norm preimages, retaining differences and the original arithmetic kernel cocycle for every automorphism.
Named downstream consumer: the exact selected literal mu19 torsor-cocycle pushforward and nineteen Kummer unit condition.
-/
import Definitions.Def_MazurTransfer_OriginalIntegralNormTorsorArithmeticPointsData20261020
import Theorems.Thm_MazurTransfer_original_integral_arithmetic_field_point_comparison_laws
noncomputable section
open MazurTransfer

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13LocalIntegralCoefficientMaps Order13ExceptionalNineteenFlatNormFibres
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeIntegralNormExtensions
open Order13GoodPrimeIntegralNormGroupLaws Order13GoodPrimeIntegralNormPointwiseUnit
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKernelGaloisAction Order13NineteenIntegralPointCompatibility
open RelativeNormPreimagePointTorsor RelativeNormPreimageRepresentation
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13IntegralNormTorsorArithmeticPoints
local notation "R" => LocalRing 19
attribute [local instance] MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.instIsCommMonObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralNormTorsorArithmeticPoints
attribute [local instance] MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.instFactPrimeOfNatNat_order13IntegralNormTorsorArithmeticPoints
attribute [local instance] MazurTransfer.Order13IntegralNormTorsorArithmeticPoints.instGrpObjOverSchemeSpecOfRatMkToBaseActualPicard_order13IntegralNormTorsorArithmeticPoints
namespace MazurTransfer.OriginalIntegralNormTorsorArithmeticPointsBoundary20261020
end MazurTransfer.OriginalIntegralNormTorsorArithmeticPointsBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the ACTUAL integral norm torsor's field points
with the PREVIOUSLY FIXED rational norm preimages, retaining differences
and the original arithmetic Galois kernel cocycle for EVERY automorphism.
Named downstream consumer: exact selected mu19 torsor-cocycle pushforward
and the nineteen Kummer unit condition.
-/

noncomputable section
namespace MazurTransfer.OriginalIntegralNormTorsorArithmeticPointsProof20261020
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13LocalIntegralCoefficientMaps Order13ExceptionalNineteenFlatNormFibres
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeIntegralNormExtensions
open Order13GoodPrimeIntegralNormGroupLaws Order13GoodPrimeIntegralNormPointwiseUnit
open Order13ActualPicardDiamondSchemeEndomorphism Order13SameIntegralPicardRationalSchemeComparison
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKernelGaloisAction Order13NineteenIntegralPointCompatibility
open RelativeNormPreimagePointTorsor RelativeNormPreimageRepresentation
open scoped CategoryTheory.MonObj



variable (K : Type) [Field K] [CharZero K]
variable [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
variable (a : RationalPoints)






theorem fieldPoint_norm (b : Points K) :
    fixedActualFieldPointEquiv K (b ≫ φ) =
      NeronModelInfra.schemeHomOverComp (fixedActualFieldPointEquiv K b)
        (integralNorm 19 nineteen_good φ) :=
  MazurTransfer.original_integral_arithmetic_field_point_comparison_laws.2.2.2.1 19 nineteen_good K φ b



theorem fieldPoint_inv (b : Points K) :
    fixedActualFieldPointEquiv K b⁻¹ = (localLaw 19 nineteen_good).inv
      (FieldAutomorphismOverPointAction.fieldBase R K) (fixedActualFieldPointEquiv K b) := by
  letI := (localLaw 19 nineteen_good).pointGroup (FieldAutomorphismOverPointAction.fieldBase R K)
  let map : Points K →* SchemeHomOver (FieldAutomorphismOverPointAction.fieldBase R K) integralModel.toBase :=
    { toFun := fixedActualFieldPointEquiv K
      map_one' := MazurTransfer.original_integral_arithmetic_field_point_comparison_laws.2.1 19 nineteen_good K
      map_mul' := MazurTransfer.original_integral_arithmetic_field_point_comparison_laws.2.2.1 19 nineteen_good K }
  exact map_inv map b





theorem kernel_difference_point_comparison (x y : rationalPreimages K φ a) :
    fixedKernelPointEquiv K φ (rationalDifference K φ a x y) =
      RelativeNormPreimagePointTorsor.difference (localLaw 19 nineteen_good)
        (integralNorm 19 nineteen_good φ) (normOne φ) (normMul φ)
        (preimageEquiv K φ a x) (preimageEquiv K φ a y) := by
  apply Subtype.ext
  change fixedActualFieldPointEquiv K (x.val * y.val⁻¹) =
    (localLaw 19 nineteen_good).mul (FieldAutomorphismOverPointAction.fieldBase R K)
      (fixedActualFieldPointEquiv K x.val)
      ((localLaw 19 nineteen_good).inv (FieldAutomorphismOverPointAction.fieldBase R K)
        (fixedActualFieldPointEquiv K y.val))
  exact (MazurTransfer.original_integral_arithmetic_field_point_comparison_laws.2.2.1 19 nineteen_good K x.val y.val⁻¹).trans
    (congrArg (fun z => (localLaw 19 nineteen_good).mul
      (FieldAutomorphismOverPointAction.fieldBase R K) (fixedActualFieldPointEquiv K x.val) z)
      (fieldPoint_inv K y.val))



theorem preimageEquiv_arithmetic_act (σ : K ≃ₐ[ℚ] K) (b : rationalPreimages K φ a) :
    (preimageEquiv K φ a (arithmeticPreimageAct K φ a σ b)).val =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (MazurTransfer.original_integral_arithmetic_field_point_comparison_laws.2.2.2.2.1 19 K σ)
        (preimageEquiv K φ a b).val :=
  MazurTransfer.original_integral_arithmetic_field_point_comparison_laws.2.2.2.2.2 19 nineteen_good K σ b.val

theorem original_kernel_cocycle_is_torsor_difference
    (σ : K ≃ₐ[ℚ] K) (b : rationalPreimages K φ a) :
    fixedKernelPointEquiv K φ (kernelCocycle K φ a b.val b.property σ) =
      RelativeNormPreimagePointTorsor.difference (localLaw 19 nineteen_good)
        (integralNorm 19 nineteen_good φ) (normOne φ) (normMul φ)
        (preimageEquiv K φ a (arithmeticPreimageAct K φ a σ b)) (preimageEquiv K φ a b) := by
  have h : kernelCocycle K φ a b.val b.property σ =
      rationalDifference K φ a (arithmeticPreimageAct K φ a σ b) b := Subtype.ext rfl
  rw [h]
  exact kernel_difference_point_comparison K φ a _ _

end MazurTransfer.OriginalIntegralNormTorsorArithmeticPointsProof20261020

theorem solution : (∀ (K : Type) [Field K] [CharZero K] [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ], ∀ (b : Points K),
fixedActualFieldPointEquiv K (b ≫ φ) =
      NeronModelInfra.schemeHomOverComp (fixedActualFieldPointEquiv K b)
        (integralNorm 19 nineteen_good φ)) ∧ (∀ (K : Type) [Field K] [CharZero K] [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K], ∀ (b : Points K),
fixedActualFieldPointEquiv K b⁻¹ = (localLaw 19 nineteen_good).inv
      (FieldAutomorphismOverPointAction.fieldBase R K) (fixedActualFieldPointEquiv K b)) ∧ (∀ (K : Type) [Field K] [CharZero K] [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (a : RationalPoints), ∀ (x y : rationalPreimages K φ a),
fixedKernelPointEquiv K φ (rationalDifference K φ a x y) =
      RelativeNormPreimagePointTorsor.difference (localLaw 19 nineteen_good)
        (integralNorm 19 nineteen_good φ) (normOne φ) (normMul φ)
        (preimageEquiv K φ a x) (preimageEquiv K φ a y)) ∧ (∀ (K : Type) [Field K] [CharZero K] [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (a : RationalPoints), ∀ (σ : K ≃ₐ[ℚ] K) (b : rationalPreimages K φ a),
(preimageEquiv K φ a (arithmeticPreimageAct K φ a σ b)).val =
      GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom σ.toRingHom))
        (MazurTransfer.original_integral_arithmetic_field_point_comparison_laws.2.2.2.2.1 19 K σ)
        (preimageEquiv K φ a b).val) ∧ (∀ (K : Type) [Field K] [CharZero K] [aRK : Algebra R K] [tRQ : IsScalarTower R ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (a : RationalPoints), ∀ (σ : K ≃ₐ[ℚ] K) (b : rationalPreimages K φ a),
fixedKernelPointEquiv K φ (kernelCocycle K φ a b.val b.property σ) =
      RelativeNormPreimagePointTorsor.difference (localLaw 19 nineteen_good)
        (integralNorm 19 nineteen_good φ) (normOne φ) (normMul φ)
        (preimageEquiv K φ a (arithmeticPreimageAct K φ a σ b)) (preimageEquiv K φ a b)) := by
  exact ⟨MazurTransfer.OriginalIntegralNormTorsorArithmeticPointsProof20261020.fieldPoint_norm, MazurTransfer.OriginalIntegralNormTorsorArithmeticPointsProof20261020.fieldPoint_inv, MazurTransfer.OriginalIntegralNormTorsorArithmeticPointsProof20261020.kernel_difference_point_comparison, MazurTransfer.OriginalIntegralNormTorsorArithmeticPointsProof20261020.preimageEquiv_arithmetic_act, MazurTransfer.OriginalIntegralNormTorsorArithmeticPointsProof20261020.original_kernel_cocycle_is_torsor_difference⟩
#print axioms solution
