-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormContinuousH1Exponent.actualPiConjugateNormQuotient_killed_nineteen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T01:14:10.97715+00:00
-- url     : https://prove2.me/submissions/41ae031d-c350-47d2-acc3-ed6754ca062f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric norm kernels have exponent nineteen,
so their continuous H1 groups and rational norm quotients are killed by
nineteen. This does not assert finiteness. Named downstream consumer:
the finite-field structure and dimension bound in the actual Selmer group.
-/
import Definitions.Def_MazurTransfer_Order13ActualSpecificContinuousNormH1ExponentData
noncomputable section
open MazurTransfer
open MazurTransfer.Order13ActualPicardNormContinuousH1Exponent
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualActualPiConjugateNormQuotientKilledNineteenSourceProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualActualPiConjugateNormQuotientKilledNineteenSourceProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualActualPiConjugateNormQuotientKilledNineteenSourceProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualActualPiConjugateNormQuotientKilledNineteenSourceProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormAlgebraicCohomology
open Order13ActualPicardNormAlgebraicKummerInjection
open Order13ActualPicardNormContinuousCohomology
open Order13ActualPicardNormContinuousCocycles
local instance actualActualPiConjugateNormQuotientKilledNineteenSourceProvider1020261018 : IsGalois ℚ (AlgebraicClosure ℚ) := canonicalClosureGalois
open Order13ActualPicardNormContinuousKummerInjection
local instance actualActualPiConjugateNormQuotientKilledNineteenSourceProvider1120261018 : IsFinite schemePi.left :=
  (Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).1.1
local instance actualActualPiConjugateNormQuotientKilledNineteenSourceProvider1220261018 : IsFinite schemePiConjugate.left :=
  (Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).2.1

theorem solution (x : NormQuotient schemePiConjugate) :
    x ^ 19 = 1 := by
  apply actualPiConjugateAlgebraicClosureContinuousKummerGroupHom_injective
  rw [map_pow, map_one]
  change (19 : ℕ) • (actualPiConjugateAlgebraicClosureContinuousKummerGroupHom x).toAdd = 0
  exact actualPiConjugateContinuousH1_killed_nineteen _


#print axioms solution
