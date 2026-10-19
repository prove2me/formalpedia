-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardRationalNormComparison.rationalClass_schemePiConjugate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T18:35:24.914544+00:00
-- url     : https://prove2.me/submissions/f6e22c8f-066b-42b5-a63c-0ad7fa45b19e

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
local instance rationalClassPiConjugateProofOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance rationalClassPiConjugateProofOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local instance rationalClassPiConjugateProofOriginalGroupProvider20261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
local instance rationalClassPiConjugateProofOriginalCommProvider20261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj
local instance rationalClassPiConjugateProofOriginalPiHomProvider20261018 : IsMonHom schemePi := schemePi_isMonHom
local instance rationalClassPiConjugateProofOriginalConjugateHomProvider20261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

variable (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)

theorem solution (a : RationalPoints) :
    (rationalClassEquiv 𝒱 (a ≫ schemePiConjugate)).toAdd =
      Order13ActualDiamondPicardEndomorphisms.piConjugate ((rationalClassEquiv 𝒱 a).toAdd) := by
  simp only [schemePiConjugate, MonObj.comp_mul, MonObj.comp_pow,
    GrpObj.comp_inv, Category.comp_id]
  rw [map_mul, map_inv, map_pow, map_pow]
  change (5 : ℕ) • (rationalClassEquiv 𝒱 a).toAdd +
    -((2 : ℕ) • (rationalClassEquiv 𝒱 (a ≫ schemeDiamond)).toAdd) = _
  rw [rationalClass_schemeDiamond]
  exact (sub_eq_add_neg _ _).symm

#print axioms solution
