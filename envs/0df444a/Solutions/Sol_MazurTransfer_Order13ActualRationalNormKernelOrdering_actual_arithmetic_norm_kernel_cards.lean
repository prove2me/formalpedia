-- Prove2me | solution 1 for MazurTransfer.Order13ActualRationalNormKernelOrdering.actual_arithmetic_norm_kernel_cards
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T20:02:23.203262+00:00
-- url     : https://prove2.me/submissions/d65a8447-29a4-4d7b-be68-131713b6cef9

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib
import Definitions.Def_MazurTransfer_Order13InfinityDivisorClassData
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Theorems.Thm_MazurTransfer_Order13InfinityClassActualNormKernels_actual_piConjugate_infinityClass
import Theorems.Thm_MazurTransfer_Order13InfinityPicardClassOrder_infinityClass_order
import Theorems.Thm_MazurTransfer_Order13ArithmeticNormKernelCardinality_actual_arithmetic_norm_kernel_card_dichotomy
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the nonzero infinity class lies in the conjugate norm kernel and orders the accepted cardinality dichotomy. Named downstream consumer: rational norm-kernel ordering and fixed-part dimensions. The original unused affine cover parameter is retained explicitly.
-/
noncomputable section
open MazurTransfer AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13InfinityPicardClassOrder
open MazurTransfer.Order13ActualDiamondPicardEndomorphisms
local instance arithmeticNormCardsInfinityOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem solution (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    Nat.card pi.ker = 1 ∧ Nat.card piConjugate.ker = 19 := by
  have hne : infinityClass ≠ 0 := by
    intro h
    have ho := infinityClass_order
    rw [h, addOrderOf_zero] at ho
    norm_num at ho
  rcases Order13ArithmeticNormKernelCardinality.actual_arithmetic_norm_kernel_card_dichotomy with h | h
  · haveI : Subsingleton piConjugate.ker := (Nat.card_eq_one_iff_unique.mp h.2).1
    have hx : infinityClass ∈ piConjugate.ker := Order13InfinityClassActualNormKernels.actual_piConjugate_infinityClass
    have he : (⟨infinityClass,hx⟩ : piConjugate.ker) = 0 := Subsingleton.elim _ _
    exact False.elim (hne (congrArg Subtype.val he))
  · exact h
#print axioms solution
