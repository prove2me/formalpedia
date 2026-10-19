-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormSubgroupRestrictionF19.restrictedH1_killed_nineteen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T00:56:36.41149+00:00
-- url     : https://prove2.me/submissions/bf3ea88a-bb25-48f6-9573-e11026f32809

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric norm kernels have exponent nineteen,
so their continuous H1 groups and rational norm quotients are killed by
nineteen. This does not assert finiteness. Named downstream consumer:
the finite-field structure and dimension bound in the actual Selmer group.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionWithCoboundaryLawDataV220261018
noncomputable section

open MazurTransfer
open MazurTransfer.Order13ActualPicardNormContinuousCocycles
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormRestrictedContinuousH1ExponentSourceProvider20261018920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormRestrictedContinuousH1ExponentSourceProvider202610181020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormRestrictedContinuousH1ExponentSourceProvider202610181120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormRestrictedContinuousH1ExponentSourceProvider202610181220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance actualNormRestrictedContinuousH1ExponentSourceProvider202610181320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormRestrictedContinuousH1ExponentSourceProvider202610181420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormRestrictedContinuousH1ExponentSourceProvider202610181520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormRestrictedContinuousH1ExponentSourceProvider202610181620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology
open MazurTransfer.Order13ActualPicardNormContinuousCohomology

open MazurTransfer.Order13ActualPicardNormSubgroupRestriction

theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [IsFinite φ.left] (S : Subgroup (K ≃ₐ[ℚ] K)) (h19 : ∀ z : Kernel K φ, z ^ 19 = 1)
    (x : localContinuousH1 K φ S) : (19 : ℕ) • x = 0 := by
  refine Quotient.inductionOn x ?_
  intro z
  have hz : (19 : ℕ) • z = 0 := by
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro σ
    change (Additive.toMul (z.val σ) : Kernel K φ) ^ 19 = 1
    exact h19 _
  change (19 : ℕ) • ContinuousFirstCohomologyPresentation.classMap S (Kernel K φ) z = 0
  rw [← map_nsmul, hz, map_zero]


#print axioms solution
