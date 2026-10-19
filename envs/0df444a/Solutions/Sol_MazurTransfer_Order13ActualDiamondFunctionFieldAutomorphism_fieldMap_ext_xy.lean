-- Prove2me | solution 1 for MazurTransfer.Order13ActualDiamondFunctionFieldAutomorphism.fieldMap_ext_xy
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T11:21:23.461022+00:00
-- url     : https://prove2.me/submissions/3a23cd0d-7f18-4d7c-9a4d-ff0ed01a9a4c

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: maps of the actual rational curve function field are determined
by the two literal ordinary coordinates.
Named downstream consumer: diamond field-automorphism inverse identities. -/
import Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldMap
noncomputable section
open Polynomial MazurTransfer
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13ActualOrdinaryPolynomialTranscendence Order13ActualDiamondFunctionFieldMap
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
theorem solution (f g : actualCurveFunctionField ℚ →+* actualCurveFunctionField ℚ)
    (hx : f (xImage ℚ) = g (xImage ℚ)) (hy : f (yImage ℚ) = g (yImage ℚ)) : f = g := by
  apply IsFractionRing.ringHom_ext (A := CoordinateRing ℚ)
  have H : f.comp (algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ)) =
      g.comp (algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ)) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext'
      · exact Subsingleton.elim _ _
      · exact hx
    · exact hy
  exact fun b => RingHom.congr_fun H b
#print axioms solution
