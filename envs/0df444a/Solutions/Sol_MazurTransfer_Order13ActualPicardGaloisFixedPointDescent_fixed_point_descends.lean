-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGaloisFixedPointDescent.fixed_point_descends
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T22:18:20.77798+00:00
-- url     : https://prove2.me/submissions/54947de1-42ce-4a06-9118-25cbcf0ce02a

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: rational points of the SAME represented Picard are
exactly its Galois-fixed geometric points, with their actual group law.
Named downstream consumer: algebraic norm Kummer injectivity.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
import Theorems.Thm_MazurTransfer_GaloisFixedOverPointDescent_exists_unique_descent
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
local instance actualPicardFixedPointDescentProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualPicardFixedPointDescentProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualPicardFixedPointDescentProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualPicardFixedPointDescentProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (b : Points K)
    (hb : ∀ σ : K ≃ₐ[ℚ] K, actionHom K σ b = b) :
    ∃! a : RationalPoints, rationalPoint K a = b :=
  MazurTransfer.GaloisFixedOverPointDescent.exists_unique_descent actualPicard.toBase b hb

#print axioms solution
