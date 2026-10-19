-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardDimensionTwo.actual_represented_picard_smooth_dimension_two
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T09:16:57.250667+00:00
-- url     : https://prove2.me/submissions/3d71aeac-b39e-4b2d-8a25-01a6959f96cb

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
import Definitions.Def_MazurTransfer_Order13ActualCurveModel
import Theorems.Thm_MazurTransfer_order13_actual_function_field_invariants
import Definitions.Def_MazurTransfer_Order13FieldHyperellipticFixedFieldData
import Theorems.Thm_AlgebraicCurve_CurveModel_smoothOfRelativeDimension_genusFF_of_representsRelSubPic
noncomputable section
universe u
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra AlgebraicCurve GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel

def originalGenusTwoModelForPicardDimension20261018
    (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)] [IsAlgClosed K] :
    CurveModel K (actualCurveFunctionField K) :=
  Order13ActualArithmeticCurveModel.actualCurveModel K

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
local instance actualPicardDimensionOriginalUnit104Provider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

theorem solution
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroCut (curveToBase K) ε) D) :
    SmoothOfRelativeDimension 2 D.toBase := by
  have hdim := CurveModel.smoothOfRelativeDimension_genusFF_of_representsRelSubPic
    K (actualCurveFunctionField K)
    ⟨Order13PellActualOrdinaryChart.xImage K,
      Order13FieldOrdinaryPolynomialTranscendence.xImage_transcendental K,
      Order13FieldHyperellipticFixedField.curveField_finite K⟩
    (originalGenusTwoModelForPicardDimension20261018 K) ε D h
  have hg : genusFF K (actualCurveFunctionField K) = 2 :=
    (MazurTransfer.order13_actual_function_field_invariants K (by norm_num : (104 : K) ≠ 0)).2.2.2.1
  rw [hg] at hdim
  exact hdim


#print axioms solution
