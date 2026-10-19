-- Prove2me | solution 1 for MazurTransfer.Order13PellActualInfinityValuations.pellFunction_ord_at_positive
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T12:16:50.767193+00:00
-- url     : https://prove2.me/submissions/b19f203b-207d-4bfa-b9f2-6f67170542a8

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two actual reciprocal localizations define genuine
places of the literal rational scheme function field, and z has order one.
Named downstream consumer: the Pell principal-divisor formula on that field.
The identification with the two infinity section centers is separate work.
-/
import Definitions.Def_MazurTransfer_Order13ActualInfinityValuationData
import Definitions.Def_MazurTransfer_Order13PellInfinityLocalOrders
noncomputable section
open MazurTransfer
open MazurTransfer.Order13PellActualInfinityValuations
open AlgebraicGeometry AlgebraicCurve IsDedekindDomain WithZero
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityLocalParameter Order13ReciprocalChartActualFunctionField
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance (a : ℚ) (ha : a ^ 2 = 1) : IsDiscreteValuationRing (LocalRing ℚ a ha) :=
  Order13InfinityDiscreteValuationRing.localRing_isDiscreteValuationRing ℚ a ha

namespace MazurTransfer.ActualPellPositiveInfinityOrderHelpers20261017
theorem normalized_plus_ord_at_positive :
    (infinityPlace 1 (Order13PellInfinityLocalOrders.positiveProof ℚ)).ord
      (algebraMap (ReciprocalRing ℚ) (actualCurveFunctionField ℚ)
        (Order13PellChartCertificate.reciprocalPlus ℚ)) = 0 := by
  rw [← localEmbedding_coordinate ℚ 1 (Order13PellInfinityLocalOrders.positiveProof ℚ)]
  exact infinityPlace_ord_isUnit _ _ _
    (Order13PellInfinityLocalOrders.plus_isUnit_at_positive ℚ (by norm_num))

end MazurTransfer.ActualPellPositiveInfinityOrderHelpers20261017
open MazurTransfer.ActualPellPositiveInfinityOrderHelpers20261017
theorem solution :
    (infinityPlace 1 (Order13PellInfinityLocalOrders.positiveProof ℚ)).ord pellFunction = -19 := by
  have hz0 : algebraMap (ReciprocalRing ℚ) (actualCurveFunctionField ℚ) (zCoordinate ℚ) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (Order13SingleSectionFiniteAlgebra.actual_reciprocal_z_ne_zero ℚ)
  have hp0 : algebraMap (ReciprocalRing ℚ) (actualCurveFunctionField ℚ)
      (Order13PellChartCertificate.reciprocalPlus ℚ) ≠ 0 := by
    rw [← localEmbedding_coordinate ℚ 1 (Order13PellInfinityLocalOrders.positiveProof ℚ)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (Order13PellInfinityLocalOrders.plus_isUnit_at_positive ℚ (by norm_num)).ne_zero
  rw [pellFunction, div_eq_mul_inv, Place.ord_mul _ hp0 (inv_ne_zero (pow_ne_zero 19 hz0)),
    normalized_plus_ord_at_positive, Place.ord_inv, ← zpow_natCast, Place.ord_zpow,
    infinityPlace_ord_z]
  norm_num


#print axioms solution
