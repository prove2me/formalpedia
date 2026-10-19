-- Prove2me | solution 1 for MazurTransfer.Order13PellOrdinaryPlaceOrders.pellFunction_ord_at_ordinary_point
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:57:15.13893+00:00
-- url     : https://prove2.me/submissions/53855fe3-da5f-47b1-af9a-5c9c6f4cd934

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: at a closed point in the actual ordinary chart, the Pell
function has order zero. Named downstream consumer: the global two-point
principal-divisor certificate on the rational order-13 curve.
-/
import Definitions.Def_MazurTransfer_Order13PellChartOverlapIdentities
import Definitions.Def_MazurTransfer_Order13ActualRationalSectionDegreeOneData
import Theorems.Thm_MazurTransfer_Order13PellActualOrdinaryChart_pellFunction_eq_ordinaryPlus
import Theorems.Thm_MazurTransfer_PlaceOrderOfRangeUnit_ord_image_unit
import Theorems.Thm_MazurTransfer_AffineOpenChartFunctionFieldNaturality_coordinate_embedding_via_stalk
noncomputable section
open MazurTransfer
open AlgebraicGeometry CategoryTheory AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13PellChartCertificate
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem solution
    (p : Spec (.of (CoordinateRing ℚ)))
    (x : closedPoints (curveScheme ℚ)) (hx : ordinaryChartMap ℚ p = x.1) :
    (actualPlaceOfPoint ℚ x).ord Order13PellActualInfinityValuations.pellFunction = 0 := by
  let b := (asIso ((ordinaryChartMap ℚ).stalkMap p)).inv.hom
    ((StructureSheaf.toStalk (CoordinateRing ℚ) p).hom (ordinaryPlus ℚ))
  have hb : IsUnit b := ordinaryPlus_isUnit.map
    (((asIso ((ordinaryChartMap ℚ).stalkMap p)).inv.hom).comp
      (StructureSheaf.toStalk (CoordinateRing ℚ) p).hom)
  have H := congrArg (fun f => f.hom (ordinaryPlus ℚ))
    (AffineOpenChartFunctionFieldNaturality.coordinate_embedding_via_stalk
      (.of (CoordinateRing ℚ)) (ordinaryChartMap ℚ) p)
  have Hrange :
      (algebraMap ((curveScheme ℚ).presheaf.stalk (ordinaryChartMap ℚ p))
        (actualCurveFunctionField ℚ)).range = (actualPlaceOfPoint ℚ x).toValuationSubring.toSubring := by
    rw [hx]
    exact actualPlaceOfPoint_stalk_range ℚ x
  rw [pellFunction_eq_ordinaryPlus]
  change (actualPlaceOfPoint ℚ x).ord
    (AffineOpenChartFunctionField.coordinateEmbedding (.of (CoordinateRing ℚ))
      (ordinaryChartMap ℚ) (ordinaryPlus ℚ)) = 0
  change AffineOpenChartFunctionField.coordinateEmbedding (.of (CoordinateRing ℚ))
    (ordinaryChartMap ℚ) (ordinaryPlus ℚ) =
    algebraMap ((curveScheme ℚ).presheaf.stalk (ordinaryChartMap ℚ p)) (actualCurveFunctionField ℚ) b at H
  rw [H]
  exact PlaceOrderOfRangeUnit.ord_image_unit ℚ (actualCurveFunctionField ℚ)
    ((curveScheme ℚ).presheaf.stalk (ordinaryChartMap ℚ p)) (actualPlaceOfPoint ℚ x)
    (algebraMap _ _) Hrange b hb


#print axioms solution
