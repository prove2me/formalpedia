-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelFiniteModule.kernel_finite
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T22:42:30.068491+00:00
-- url     : https://prove2.me/submissions/5b6f7aea-53b8-40b5-b677-5b445758db6d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric norm kernels are finite groups,
and their exponent nineteen makes them finite modules over F19.
Named downstream consumer: finite splitting fields and Galois module
structure needed for the actual norm Selmer bound.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
import Theorems.Thm_MazurTransfer_FiniteRationalFibreGeometricPoints_finite_preimages
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormKernelGaloisAction Order13ActualPicardGaloisFixedPointDescent
open scoped CategoryTheory.MonObj
local instance actualNormKernelFiniteProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormKernelFiniteProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
theorem solution (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] : Finite (Kernel K φ) := by
  let F := {b : Points K // b ≫ φ = rationalPoint K (1 : RationalPoints)}
  letI : Finite F := FiniteRationalFibreGeometricPoints.finite_preimages ℚ K
    actualPicard.toBase actualPicard.toBase φ 1
  let encode (z : Kernel K φ) : F :=
    ⟨z.val, z.property.trans (map_one (rationalPointHom K)).symm⟩
  apply Finite.of_injective encode
  intro z w h
  exact Subtype.ext (congrArg Subtype.val h)

#print axioms solution
