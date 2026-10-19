-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormKummerGroupHom.quotientHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T23:16:48.423828+00:00
-- url     : https://prove2.me/submissions/1fc1fd0c-7213-457f-8bdd-729b4e558e2b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual rational norm quotient Kummer injection
preserves the group law in Mathlib algebraic H1. Continuity and local
conditions remain separate obligations.
Named downstream consumer: continuous Kummer and Selmer group bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerGenericGroupHomData
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormKummerQuotientGroupHomInjectiveProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormKummerQuotientGroupHomInjectiveProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormKummerQuotientGroupHomInjectiveProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormKummerQuotientGroupHomInjectiveProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormAlgebraicKummerInjection
open MazurTransfer.Order13ActualPicardNormKummerGroupHom
theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (hsurj : Function.Surjective (normHom K φ)) : Function.Injective (quotientHom K φ hsurj) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a a' h
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply (chosenClass_eq_iff K φ hsurj a a').mp
  exact congrArg Multiplicative.toAdd h

#print axioms solution
