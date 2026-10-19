-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGenericFieldAction.actualFieldHom_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T15:46:34.293567+00:00
-- url     : https://prove2.me/submissions/1bda033c-7cd0-4783-8607-933b81249343

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original full actualFieldHom_arithmetic contract and proof retained.
Design boundary: the original genuine scheme field action induces the
specified automorphism action on the original arithmetic Pic0 classes.
Named downstream consumer: diamond scheme action and scheme norm identities.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGenericFieldActionData
import Theorems.Thm_MazurTransfer_Order13ActualPicardArithmeticPullbackNaturality_arithmeticClass_postComp_pullback
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualCurveFieldAutomorphismLift Order13ActualDiamondGenericCurveOrder
open Order13ActualPicardArithmeticPullbackNaturality Order13ActualPicardDiamondSchemeEndomorphism
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open PicardReRigidifiedCurvePullback Order13ArithmeticPicardPointMap
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ

open Order13ActualPicardGenericFieldAction

theorem solution (σ : F ≃ₐ[ℚ] F) (𝒱 : C.TwoAffineOpenCover)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ))) actualPicard.toBase) :
    arithmeticClass ℚ 𝒱 infinitySection actualPicard actualRepresentation
        (postComp (actualFieldHom σ) a) =
      σ • arithmeticClass ℚ 𝒱 infinitySection actualPicard actualRepresentation a :=
  arithmeticClass_postComp_pullback 𝒱 infinitySection actualPicard actualRepresentation
    σ (actualFieldAction σ) a

#print axioms solution
