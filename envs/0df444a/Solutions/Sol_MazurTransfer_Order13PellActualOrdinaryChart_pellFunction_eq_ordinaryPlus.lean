-- Prove2me | solution 1 for MazurTransfer.Order13PellActualOrdinaryChart.pellFunction_eq_ordinaryPlus
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:49:39.764485+00:00
-- url     : https://prove2.me/submissions/8f36c359-d00c-486d-a1a6-188bbbb965f3

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the actual infinity-defined Pell function with
the ordinary-coordinate unit using the literal chart overlap. Named downstream
consumer: vanishing orders at all places in the ordinary affine chart.
-/
import Definitions.Def_MazurTransfer_Order13PellChartOverlapIdentities
import Definitions.Def_MazurTransfer_Order13ActualInfinityValuationData
noncomputable section
universe u
open MazurTransfer
open Order13PellActualOrdinaryChart
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellChartCertificate Order13ChartOverlapFunctionField
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

theorem solution :
    Order13PellActualInfinityValuations.pellFunction =
      algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ) (ordinaryPlus ℚ) := by
  apply (div_eq_iff (pow_ne_zero 19 (zImage_ne_zero ℚ))).mpr
  exact (ordinaryPlus_mul_zImage ℚ).symm


#print axioms solution
