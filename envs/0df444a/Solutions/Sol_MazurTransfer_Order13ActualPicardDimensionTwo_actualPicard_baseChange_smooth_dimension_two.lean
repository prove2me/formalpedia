-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardDimensionTwo.actualPicard_baseChange_smooth_dimension_two
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T09:32:16.844652+00:00
-- url     : https://prove2.me/submissions/9f84eece-1155-42f2-9def-18ef30a3c247

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: relative dimension two for every represented degree-zero
Picard of the actual order-13 curve over an algebraically closed field of
characteristic zero, including the geometric base change of the SAME rational
Picard used by both nineteen norm maps.
Named downstream consumer: geometric nineteen-torsion cardinality and the
geometric dimensions of those two actual norm kernels.
Uses complete official Anthropic FLT proofs at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13LiteralFibrePicardRepresentation
import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardDimensionTwo_actual_represented_picard_smooth_dimension_two
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra AlgebraicCurve GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13IntegralPicardLiteralFibreRepresentations
open Order13ActualPicardDimensionTwo
attribute [local instance] Order13ActualRationalFunctionFieldTower.actualRatFuncTowerOriginalFactProvider20261018

theorem solution
    (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    SmoothOfRelativeDimension 2 (actualPicard.baseChange K).toBase := by
  let D := literalFibreDesignation ℚ K actualPicard
  have h := (literal_fibre_representation ℚ K actualPicard actualRepresentation).some
  exact actual_represented_picard_smooth_dimension_two K
    (Order13IntegralSections.positiveInfinitySection K) D h

#print axioms solution
