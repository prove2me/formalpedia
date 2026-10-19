-- Prove2me | solution 1 for MazurTransfer.Order13PellActualInfinityValuations.infinityPlace_ord_associated_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T12:12:33.010422+00:00
-- url     : https://prove2.me/submissions/fb062442-e856-4f65-b0d5-56ca8996952d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two actual reciprocal localizations define genuine
places of the literal rational scheme function field, and z has order one.
Named downstream consumer: the Pell principal-divisor formula on that field.
The identification with the two infinity section centers is separate work.
-/
import Definitions.Def_MazurTransfer_Order13ActualInfinityValuationData
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

theorem solution (a : ℚ) (ha : a ^ 2 = 1)
    (b : LocalRing ℚ a ha) (n : ℕ) (hb : Associated b (z ℚ a ha ^ n)) :
    (infinityPlace a ha).ord (algebraMap (LocalRing ℚ a ha) (actualCurveFunctionField ℚ) b) = n := by
  have hb0 := hb.ne_zero_iff.mpr (pow_ne_zero n (Order13InfinityDiscreteValuationRing.z_ne_zero ℚ a ha))
  obtain ⟨u, hu⟩ := hb
  let φ : LocalRing ℚ a ha →+* actualCurveFunctionField ℚ := algebraMap _ _
  let v := infinityPlace a ha
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hzord : v.ord (φ (z ℚ a ha)) = 1 := by
    change v.ord (localEmbedding ℚ a ha (algebraMap (ReciprocalRing ℚ)
      (LocalRing ℚ a ha) (zCoordinate ℚ))) = 1
    rw [localEmbedding_coordinate]
    exact infinityPlace_ord_z a ha
  calc
    v.ord (φ b) = v.ord (φ (b * (u : LocalRing ℚ a ha))) := by
      rw [map_mul, v.ord_mul ((map_ne_zero_iff φ hinj).mpr hb0)
        ((map_ne_zero_iff φ hinj).mpr u.ne_zero), infinityPlace_ord_isUnit a ha _ u.isUnit,
        add_zero]
    _ = v.ord (φ (z ℚ a ha ^ n)) := congrArg (fun x => v.ord (φ x)) hu
    _ = n := by
      rw [map_pow, ← zpow_natCast, v.ord_zpow, hzord, mul_one]


#print axioms solution
