-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardRationalNormComparison.rationalClass_schemePi
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T18:29:11.214038+00:00
-- url     : https://prove2.me/submissions/016ef814-20a8-4527-ac65-a1f6f0296acf

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalNormComparisonOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardRationalNormComparison_rationalClass_schemeDiamond
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT Picard and divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the original rational arithmetic class equivalence intertwines the actual scheme endomorphism with its arithmetic Picard endomorphism. Named downstream consumer: the original rational norm-kernel equivalences and cardinality transport.
-/
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardGeometricDiamondGroupAction Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardSchemeNormGroupHom
open scoped CategoryTheory.MonObj
open MazurTransfer.Order13ActualPicardRationalNormComparison
open MazurTransfer.Order13ActualPicardGenericFieldAction
local instance rationalClassPiProofOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance rationalClassPiProofOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local instance rationalClassPiProofOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
local instance rationalClassPiProofOriginalCommProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj
local instance rationalClassPiProofOriginalPiHomProvider20261018 : IsMonHom schemePi := schemePi_isMonHom
local instance rationalClassPiProofOriginalConjugateHomProvider20261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

variable (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)

theorem solution (a : RationalPoints) :
    (rationalClassEquiv 𝒱 (a ≫ schemePi)).toAdd =
      Order13ActualDiamondPicardEndomorphisms.pi ((rationalClassEquiv 𝒱 a).toAdd) := by
  simp only [schemePi, MonObj.comp_mul, MonObj.comp_pow, Category.comp_id]
  rw [map_mul, map_pow, map_pow]
  change (3 : ℕ) • (rationalClassEquiv 𝒱 a).toAdd +
    (2 : ℕ) • (rationalClassEquiv 𝒱 (a ≫ schemeDiamond)).toAdd = _
  rw [rationalClass_schemeDiamond]
  rfl

#print axioms solution
