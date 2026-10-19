-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormContinuousCohomology.continuousClassOfLift_zero_iff_rational_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T23:58:43.833259+00:00
-- url     : https://prove2.me/submissions/0faddd47-5b4f-4e28-9815-af07b3b7eec6

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual continuous kernel cocycles determine classes
in continuous H1, defined as continuous cocycles modulo coboundaries.
These classes have an injective forgetful map to Mathlib algebraic H1.
Named downstream consumer: actual continuous Kummer quotient injections.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormContinuousH1ClassData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormAlgebraicCohomology_classOfLift_zero_iff_rational_norm_preimage
import Theorems.Thm_MazurTransfer_FiniteRationalFibreGaloisOrbit_stabilizer_isOpen
import Theorems.Thm_MazurTransfer_DiscreteOrbitContinuityFromOpenStabilizer_continuous_orbit

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
local instance actualContinuousH1ZeroCriterionSourceProvider920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualContinuousH1ZeroCriterionSourceProvider1020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualContinuousH1ZeroCriterionSourceProvider1120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualContinuousH1ZeroCriterionSourceProvider1220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance actualContinuousH1ZeroCriterionSourceProvider1320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance actualContinuousH1ZeroCriterionSourceProvider1420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualContinuousH1ZeroCriterionSourceProvider1520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualContinuousH1ZeroCriterionSourceProvider1620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology
open MazurTransfer.Order13ActualPicardNormContinuousCohomology
theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] (a : RationalPoints) (b : Points K)
    (hb : b ≫ φ = rationalPoint K a) :
    continuousClassOfLift K φ a b hb = 0 ↔ ∃ c : RationalPoints, c ≫ φ = a := by
  rw [← (ContinuousFirstCohomologyPresentation.forgetH1_injective
    (K ≃ₐ[ℚ] K) (Kernel K φ)).eq_iff, map_zero, forget_continuousClassOfLift]
  exact classOfLift_zero_iff_rational_norm_preimage K φ a b hb


#print axioms solution
