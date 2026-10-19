-- Prove2me | solution 1 for MazurTransfer.Order13InfinityClassActualNormKernels.actual_rho_eq_field_rho
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T19:26:58.956632+00:00
-- url     : https://prove2.me/submissions/96ff9858-666f-4698-bdcc-a0162ded3c1e

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Definitions.Def_MazurTransfer_Order13FieldDiamondPicardEndomorphismsData
import Theorems.Thm_MazurTransfer_Order13InfinityClassActualNormKernels_actual_diamond_eq_field_diamond
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original actual rational Picard diamond action equals the specialization of the field-parametric Picard diamond action. Named downstream consumer: the infinity-class eigenvalue and actual conjugate-norm kernel ordering. The original complete equality is retained.
-/
noncomputable section
open MazurTransfer AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13InfinityClassActualNormKernels
local instance actualRhoFieldEqualityOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance actualRhoFieldEqualityOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem solution : Order13ActualDiamondPicardEndomorphisms.rho =
    Order13FieldDiamondPicardEndomorphisms.rho ℚ := by
  apply AddMonoidHom.ext
  intro c
  change Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv • c =
    Order13FieldDiamondFunctionFieldAutomorphism.diamondAlgEquiv ℚ • c
  rw [actual_diamond_eq_field_diamond]

#print axioms solution
