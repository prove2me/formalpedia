-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardRationalNormKernelCardinality.actual_rational_norm_kernels_finite
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T18:49:11.777691+00:00
-- url     : https://prove2.me/submissions/bff7b690-338b-4379-bb98-9ceaccf26347

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalNormKernelEquivalencesOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ArithmeticNormKernelCardinality_actual_arithmetic_norm_kernel_card_product
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
local instance rationalNormKernelFiniteOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

theorem solution (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) : Finite rationalPi.ker ∧ Finite rationalPiConjugate.ker := by
  obtain ⟨hf, hg, _⟩ := Order13ArithmeticNormKernelCardinality.actual_arithmetic_norm_kernel_card_product
  letI := hf
  letI := hg
  exact ⟨Finite.of_equiv _ (rationalPiKernelEquiv 𝒱).symm,
    Finite.of_equiv _ (rationalPiConjugateKernelEquiv 𝒱).symm⟩

#print axioms solution
