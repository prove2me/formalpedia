-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormContinuousCocycles.kernelCocycle_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T23:41:06.635647+00:00
-- url     : https://prove2.me/submissions/028538a1-74be-4871-b8a8-bf57028bb0c2

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
local instance actualKernelCocycleContinuousSourceProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualKernelCocycleContinuousSourceProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualKernelCocycleContinuousSourceProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualKernelCocycleContinuousSourceProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualKernelCocycleContinuousSourceProvider520261017 : TopologicalSpace (Points K) := pointsTopology K
local instance actualKernelCocycleContinuousSourceProvider620261017 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualKernelCocycleContinuousSourceProvider720261017 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualKernelCocycleContinuousSourceProvider820261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ


variable [IsFinite φ.left]

theorem cocyclePreimageStabilizerIsOpen20261017 (a : RationalPoints) (b : Points K)
    (hb : b ≫ φ = rationalPoint K a) :
    IsOpen {σ : K ≃ₐ[ℚ] K | actionHom K σ b = b} :=
  FiniteRationalFibreGaloisOrbit.stabilizer_isOpen ℚ K
    actualPicard.toBase actualPicard.toBase φ a b hb

theorem cocyclePreimageOrbitContinuous20261017 (a : RationalPoints) (b : Points K)
    (hb : b ≫ φ = rationalPoint K a) :
    Continuous (fun σ : K ≃ₐ[ℚ] K => actionHom K σ b) := by
  exact DiscreteOrbitContinuityFromOpenStabilizer.continuous_orbit b
    (cocyclePreimageStabilizerIsOpen20261017 K φ a b hb)

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
local instance actualKernelCocycleContinuousSourceProvider920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualKernelCocycleContinuousSourceProvider1020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualKernelCocycleContinuousSourceProvider1120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualKernelCocycleContinuousSourceProvider1220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance actualKernelCocycleContinuousSourceProvider1320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance actualKernelCocycleContinuousSourceProvider1420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualKernelCocycleContinuousSourceProvider1520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualKernelCocycleContinuousSourceProvider1620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ
theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] (a : RationalPoints) (b : Points K)
    (hb : b ≫ φ = rationalPoint K a) :
    Continuous (kernelCocycle K φ a b hb) := by
  apply Continuous.subtype_mk
  change Continuous (fun σ : K ≃ₐ[ℚ] K => actionHom K σ b * b⁻¹)
  exact (cocyclePreimageOrbitContinuous20261017 K φ a b hb).mul continuous_const


#print axioms solution
