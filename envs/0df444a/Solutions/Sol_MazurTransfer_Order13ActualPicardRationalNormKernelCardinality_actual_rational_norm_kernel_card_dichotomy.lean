-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardRationalNormKernelCardinality.actual_rational_norm_kernel_card_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T19:14:06.447904+00:00
-- url     : https://prove2.me/submissions/ab067240-9425-47a9-bacb-dd6200ed05b3

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalNormKernelEquivalencesOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ArithmeticNormKernelCardinality_actual_arithmetic_norm_kernel_card_dichotomy
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT Picard and divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: transport the original arithmetic norm-kernel cardinality statement to the rational points of the same represented Picard. Named downstream consumer: actual rational norm-kernel ordering and Galois fixed-part dimensions.
-/
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardRationalNormComparison
open Order13ActualPicardRationalNormKernelCardinality
open scoped CategoryTheory.MonObj
local instance rationalNormKernelDichotomyOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

theorem solution (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    (Nat.card rationalPi.ker = 19 ∧ Nat.card rationalPiConjugate.ker = 1) ∨
      (Nat.card rationalPi.ker = 1 ∧ Nat.card rationalPiConjugate.ker = 19) := by
  rw [Nat.card_congr (rationalPiKernelEquiv 𝒱),
    Nat.card_congr (rationalPiConjugateKernelEquiv 𝒱)]
  exact Order13ArithmeticNormKernelCardinality.actual_arithmetic_norm_kernel_card_dichotomy

#print axioms solution
