-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormKummerCocycles.change_preimage_kernel_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T22:03:20.66056+00:00
-- url     : https://prove2.me/submissions/851b20ff-2094-4329-8bbf-9d0ed5e97c2f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: rational points on the SAME represented Picard give
kernel-valued algebraic Galois cocycles for each actual norm map; the
kernels are killed by nineteen. This does not assert continuity, Galois
descent of fixed points, or a Selmer bound.
Named downstream consumer: continuous norm Kummer classes and local conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerData
noncomputable section
namespace MazurTransfer.ActualKummerChangePreimageGenericHelpers20261017
open MazurTransfer.EquivariantNormPreimageCocycle
variable {G H : Type*} [Group G] [CommGroup H]
variable (ρ : G → H →* H) (f : H →* H)
theorem change_preimage_in_kernel {a b b' : H} (hb : f b = a) (hb' : f b' = a) :
    f (b' * b⁻¹) = 1 := by
  simp only [map_mul, map_inv, hb, hb', mul_inv_cancel]

theorem change_preimage_coboundary (b b' : H) (σ : G) :
    difference ρ b' σ =
      ρ σ (b' * b⁻¹) * difference ρ b σ * (b' * b⁻¹)⁻¹ := by
  simp only [difference, map_mul, map_inv]
  simp [mul_assoc, mul_left_comm, mul_comm]
end MazurTransfer.ActualKummerChangePreimageGenericHelpers20261017
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open scoped CategoryTheory.MonObj
local instance actualKummerChangePreimageProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualKummerChangePreimageProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualKummerChangePreimageProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualKummerChangePreimageProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open MazurTransfer.Order13ActualPicardNormKummerCocycles
theorem solution (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (a : RationalPoints) (b b' : Points K)
    (hb : b ≫ φ = rationalPoint K a) (hb' : b' ≫ φ = rationalPoint K a) :
    (b' * b⁻¹) ≫ φ = 1 ∧ ∀ σ : K ≃ₐ[ℚ] K,
      difference K b' σ =
        actionHom K σ (b' * b⁻¹) * difference K b σ * (b' * b⁻¹)⁻¹ :=
  ⟨MazurTransfer.ActualKummerChangePreimageGenericHelpers20261017.change_preimage_in_kernel (normHom K φ) hb hb',
    MazurTransfer.ActualKummerChangePreimageGenericHelpers20261017.change_preimage_coboundary (actionHom K) b b'⟩

#print axioms solution
