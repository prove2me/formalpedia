-- Prove2me | solution 1 for MazurTransfer.order27_third_leg_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T15:06:22.939559+00:00
-- url     : https://prove2.me/submissions/217a2498-21b0-4114-92d4-27da8476badb

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5
import Theorems.Thm_MazurTransfer_order27_aggregate_products
import Theorems.Thm_MazurTransfer_order27_aggregate_coefficients
import Theorems.Thm_MazurTransfer_order27_aggregate_weight_three
import Theorems.Thm_MazurTransfer_order27_aggregate_weight_two
import Theorems.Thm_MazurTransfer_order27_aggregate_weight_one
import Theorems.Thm_MazurTransfer_order27_aggregate_weight_zero
import Theorems.Thm_MazurTransfer_order27_aggregate_weighted_sum



open MazurTorsion.Kubert

theorem solution {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3)) * ((zlTN0 f Z +
      zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) ^ 3 + (36 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f *
      (f - 1) * (f ^ 2 - f + 1) ^ 3) + 729 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) *
      (f ^ 2 - f + 1) ^ 3) ^ 2) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) ^ 2 * zlE0 f Z
      ^ 2 + (270 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) +
      26244 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2 +
      531441 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 3) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z +
      zlTN3 Z)) * zlE0 f Z ^ 4 + (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9) * zlE0 f Z ^ 6 = 0  := by
  have hTD := MazurTransfer.order27_aggregate_products.1 hM
  have hNSq := MazurTransfer.order27_aggregate_products.2.1 hM
  have hNCb := MazurTransfer.order27_aggregate_products.2.2.1 hM
  have hNSqTD := MazurTransfer.order27_aggregate_products.2.2.2.1 hM
  have hNTD := MazurTransfer.order27_aggregate_products.2.2.2.2.1 hM
  have hNTDSq := MazurTransfer.order27_aggregate_products.2.2.2.2.2.1 hM
  have hDSq := MazurTransfer.order27_aggregate_products.2.2.2.2.2.2.1 hM
  have hDCb := MazurTransfer.order27_aggregate_products.2.2.2.2.2.2.2 hM
  have hw3 := MazurTransfer.order27_aggregate_weight_three hM
  have hw2 := MazurTransfer.order27_aggregate_weight_two hM
  have hw1 := MazurTransfer.order27_aggregate_weight_one hM
  have hw0 := MazurTransfer.order27_aggregate_weight_zero hM
  have hcomb := congrArg₂ (fun a b : ℚ => a + b)
    (congrArg₂ (fun a b : ℚ => a + b)
      (congrArg₂ (fun a b : ℚ => a + b) hw3 hw2) hw1) hw0
  have hsum : _ = (0 : ℚ) := hcomb.trans (by
    simpa only [add_assoc] using MazurTransfer.order27_aggregate_weighted_sum f Z)
  rw [← hNCb, ← hNSqTD, ← hNTDSq, ← hDCb,
      ← hNSq, ← hNTD, ← hDSq, ← hTD,
      MazurTransfer.order27_aggregate_coefficients.2.2.2 f,
      MazurTransfer.order27_aggregate_coefficients.2.2.1 f,
      MazurTransfer.order27_aggregate_coefficients.2.1 f,
      MazurTransfer.order27_aggregate_coefficients.1 f] at hsum
  generalize hN : ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) = N at hsum ⊢
  generalize hE : zlE0 f Z = e at hsum ⊢
  convert hsum using 1 <;> ring

#print axioms solution
