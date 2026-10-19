-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.quotientMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T22:58:31.098726+00:00
-- url     : https://prove2.me/submissions/fca5b570-a6f4-4630-9268-83d0be378639

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the rational quotient by an actual norm map injects
into Mathlib algebraic H1 of its actual geometric norm kernel.
Continuity and local conditions are separate obligations.
Named downstream consumer: continuous Kummer and Selmer bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardAlgebraicNormQuotientKummerData
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
local instance actualNormQuotientKummerInjectiveProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormQuotientKummerInjectiveProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormQuotientKummerInjectiveProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormQuotientKummerInjectiveProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormAlgebraicCohomology
open MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection
theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (hsurj : Function.Surjective (normHom K φ)) : Function.Injective (quotientMap K φ hsurj) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a a' h
  apply QuotientGroup.eq_iff_div_mem.mpr
  exact (chosenClass_eq_iff K φ hsurj a a').mp h

#print axioms solution
