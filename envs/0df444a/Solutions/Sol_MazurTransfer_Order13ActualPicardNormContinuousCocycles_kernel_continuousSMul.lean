-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormContinuousCocycles.kernel_continuousSMul
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T23:46:11.066093+00:00
-- url     : https://prove2.me/submissions/61e88a4a-b9dc-48ac-9e80-53164e6817b3

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual norm fibres give continuous cocycles for the
Krull topology and discrete geometric kernel topology. Named downstream
consumer: continuous Kummer classes and the local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormDiscretePointTopologyExplicitPointActionDataV320261017
import Theorems.Thm_MazurTransfer_FiniteRationalFibreGaloisOrbit_stabilizer_isOpen
import Theorems.Thm_MazurTransfer_DiscreteOrbitContinuityFromOpenStabilizer_continuous_orbit

noncomputable section
namespace MazurTransfer.Order13ActualPicardNormContinuousCocycles
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider520261017 : TopologicalSpace (Points K) := pointsTopology K
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider620261017 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider720261017 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider820261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ


variable [IsFinite φ.left]

theorem preimage_stabilizer_isOpen (a : RationalPoints) (b : Points K)
    (hb : b ≫ φ = rationalPoint K a) :
    IsOpen {σ : K ≃ₐ[ℚ] K | actionHom K σ b = b} :=
  FiniteRationalFibreGaloisOrbit.stabilizer_isOpen ℚ K
    actualPicard.toBase actualPicard.toBase φ a b hb

theorem kernel_stabilizer_isOpen (z : Kernel K φ) :
    IsOpen (MulAction.stabilizer (K ≃ₐ[ℚ] K) z : Set (K ≃ₐ[ℚ] K)) := by
  have hz : z.val ≫ φ = rationalPoint K (1 : RationalPoints) := by
    calc
      z.val ≫ φ = 1 := z.property
      _ = rationalPoint K (1 : RationalPoints) := (map_one (rationalPointHom K)).symm
  have h := preimage_stabilizer_isOpen K φ 1 z.val hz
  have hs : (MulAction.stabilizer (K ≃ₐ[ℚ] K) z : Set (K ≃ₐ[ℚ] K)) =
      {σ : K ≃ₐ[ℚ] K | actionHom K σ z.val = z.val} := by
    ext σ
    change (σ • z = z) ↔ actionHom K σ z.val = z.val
    exact Subtype.ext_iff
  rw [hs]
  exact h

end MazurTransfer.Order13ActualPicardNormContinuousCocycles
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
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider1020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider1120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider1220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider1320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider1420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider1520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualKernelContinuousSMulExplicitPointActionV2SourceProvider1620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ
theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) :=
  continuousSMul_iff_stabilizer_isOpen.mpr (kernel_stabilizer_isOpen K φ)


#print axioms solution
