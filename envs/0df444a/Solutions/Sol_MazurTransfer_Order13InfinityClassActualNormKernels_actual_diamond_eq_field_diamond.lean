-- Prove2me | solution 1 for MazurTransfer.Order13InfinityClassActualNormKernels.actual_diamond_eq_field_diamond
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T19:12:45.281341+00:00
-- url     : https://prove2.me/submissions/043453de-3e48-4026-9305-82233f65dec8

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism
import Definitions.Def_MazurTransfer_Order13FieldDiamondFunctionFieldAutomorphismData
import Theorems.Thm_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism_fieldMap_ext_xy
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original actual rational diamond automorphism equals the specialization of the original field-parametric diamond automorphism. Named downstream consumer: actual_rho_eq_field_rho in Order13InfinityClassActualNormKernels, transporting the computed infinity-class eigenvalue to the actual arithmetic norm maps.
-/
noncomputable section
open MazurTransfer AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance actualFieldDiamondEqualityOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance actualFieldDiamondEqualityOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem solution :
    Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv =
      Order13FieldDiamondFunctionFieldAutomorphism.diamondAlgEquiv ℚ := by
  apply AlgEquiv.ext
  have h : Order13ActualDiamondFunctionFieldMap.diamondFieldMap =
      Order13FieldDiamondFunctionFieldMap.diamondFieldMap ℚ := by
    apply Order13ActualDiamondFunctionFieldAutomorphism.fieldMap_ext_xy
    · rw [Order13ActualDiamondFunctionFieldMap.diamondFieldMap_x,
        Order13FieldDiamondFunctionFieldMap.diamondFieldMap_x]
    · rw [Order13ActualDiamondFunctionFieldMap.diamondFieldMap_y,
        Order13FieldDiamondFunctionFieldMap.diamondFieldMap_y]
  intro z
  exact RingHom.congr_fun h z

#print axioms solution
