-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormContinuousKummerInjection.continuousQuotientHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T00:10:42.073448+00:00
-- url     : https://prove2.me/submissions/e546c494-be90-4a2d-ba8c-5eb36e3090c0

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual rational norm quotients inject by group
homomorphisms into continuous H1 of the actual geometric norm kernels.
The checked forgetful maps recover the prior algebraic Kummer maps.
Named downstream consumer: the local Selmer conditions and rank-zero bound.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormContinuousKummerGenericGroupHomData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormKummerGroupHom_quotientHom_injective
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
local instance actualContinuousNormQuotientInjectiveSourceProvider920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualContinuousNormQuotientInjectiveSourceProvider1020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualContinuousNormQuotientInjectiveSourceProvider1120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualContinuousNormQuotientInjectiveSourceProvider1220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance actualContinuousNormQuotientInjectiveSourceProvider1320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance actualContinuousNormQuotientInjectiveSourceProvider1420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualContinuousNormQuotientInjectiveSourceProvider1520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualContinuousNormQuotientInjectiveSourceProvider1620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection
open MazurTransfer.Order13ActualPicardNormContinuousCohomology
open MazurTransfer.Order13ActualPicardNormContinuousKummerInjection
theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left]
    (hsurj : Function.Surjective (normHom K φ)) : Function.Injective (continuousQuotientHom K φ hsurj) := by
  intro x y h
  apply Order13ActualPicardNormKummerGroupHom.quotientHom_injective K φ hsurj
  apply Multiplicative.toAdd.injective
  rw [← continuousQuotientHom_forget K φ hsurj x,
    ← continuousQuotientHom_forget K φ hsurj y, h]


#print axioms solution
