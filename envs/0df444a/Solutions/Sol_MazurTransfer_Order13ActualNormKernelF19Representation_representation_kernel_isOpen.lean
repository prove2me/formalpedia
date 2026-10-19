-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelF19Representation.representation_kernel_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T01:33:14.247636+00:00
-- url     : https://prove2.me/submissions/eceb73b4-5cc7-4bc2-bcd6-3c50351eee8d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric norm kernels have exponent nineteen,
so their continuous H1 groups and rational norm quotients are killed by
nineteen. This does not assert finiteness. Named downstream consumer:
the finite-field structure and dimension bound in the actual Selmer group.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelF19RepresentationOriginalContextDataV220261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormContinuousCocycles_kernel_continuousSMul
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
local instance actualNormKernelF19RepresentationOpenKernelSourceProvider20261018920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormKernelF19RepresentationOpenKernelSourceProvider202610181020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormKernelF19RepresentationOpenKernelSourceProvider202610181120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormKernelF19RepresentationOpenKernelSourceProvider202610181220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance actualNormKernelF19RepresentationOpenKernelSourceProvider202610181320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormKernelF19RepresentationOpenKernelSourceProvider202610181420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormKernelF19RepresentationOpenKernelSourceProvider202610181520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormKernelF19RepresentationOpenKernelSourceProvider202610181620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology

open MazurTransfer.Order13ActualNormKernelF19Representation
local instance actualKernelRepresentationFiniteSourceProvider20261018 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] :
    Finite (Kernel K φ) := MazurTransfer.Order13ActualNormKernelFiniteModule.kernel_finite K φ
local instance actualKernelRepresentationModuleSourceProvider20261018 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] : Module (ZMod 19) (Additive (Kernel K φ)) :=
  MazurTransfer.Order13ActualNormKernelFiniteModule.kernelZModModule K φ
local instance actualKernelRepresentationContinuousSourceProvider20261018 (K : Type) [Field K] [CharZero K]
    [IsGalois ℚ K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom φ] [IsFinite φ.left] : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) :=
  MazurTransfer.Order13ActualPicardNormContinuousCocycles.kernel_continuousSMul K φ

theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] :
    IsOpen ((kernelRepresentation K φ).ker : Set (K ≃ₐ[ℚ] K)) := by
  have hs : ((kernelRepresentation K φ).ker : Set (K ≃ₐ[ℚ] K)) =
      ⋂ z : Kernel K φ, (MulAction.stabilizer (K ≃ₐ[ℚ] K) z : Set (K ≃ₐ[ℚ] K)) := by
    ext σ
    simp only [Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact representation_kernel_iff K φ σ
  rw [hs]
  refine isOpen_iInter_of_finite ?_
  intro z
  have h : Continuous (fun σ : K ≃ₐ[ℚ] K => σ • z) :=
    continuous_id.smul continuous_const
  change IsOpen {σ : K ≃ₐ[ℚ] K | σ • z = z}
  exact (isOpen_discrete ({z} : Set (Kernel K φ))).preimage h

#print axioms solution
