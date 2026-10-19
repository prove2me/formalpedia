-- Prove2me | solution 1 for MazurTransfer.Order13InfinityClassActualNormKernels.actual_piConjugate_infinityClass
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T19:54:50.55239+00:00
-- url     : https://prove2.me/submissions/2ad9c066-2ebc-4f18-aebf-7d00ac55d714

import Mathlib
import Definitions.Def_MazurTransfer_Order13InfinityDivisorClassData
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Theorems.Thm_MazurTransfer_Order13InfinityClassDiamondEigenvalue_twice_rho_infinityClass
import Theorems.Thm_MazurTransfer_Order13InfinityClassActualNormKernels_actual_rho_eq_field_rho
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original conjugate norm kills the original rational infinity class, using its checked diamond eigenvalue. Named downstream consumer: the arithmetic norm-kernel ordering.
-/
noncomputable section
open MazurTransfer AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13InfinityPicardClassOrder
local instance actualConjugateInfinityOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance actualConjugateInfinityOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem solution : Order13ActualDiamondPicardEndomorphisms.piConjugate infinityClass = 0 := by
  change (5 : ℕ) • infinityClass - (2 : ℕ) • Order13ActualDiamondPicardEndomorphisms.rho infinityClass = 0
  rw [Order13InfinityClassActualNormKernels.actual_rho_eq_field_rho]
  rw [← natCast_zsmul, ← natCast_zsmul]
  norm_num only
  rw [Order13InfinityClassDiamondEigenvalue.twice_rho_infinityClass]
  abel
#print axioms solution
