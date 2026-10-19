-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormKummerCocycles.actual_piConjugate_kummer_cocycle_exists
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T22:03:38.504071+00:00
-- url     : https://prove2.me/submissions/774b747f-87d6-4c1c-8cd6-7e5c7f76896d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: rational points on the SAME represented Picard give
kernel-valued algebraic Galois cocycles for each actual norm map; the
kernels are killed by nineteen. This does not assert continuity, Galois
descent of fixed points, or a Selmer bound.
Named downstream consumer: continuous norm Kummer classes and local conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerData
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePiConjugate_kernel_killed_nineteen
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricNormPreimages_schemePiConjugate_geometricPoint_surjective
noncomputable section
namespace MazurTransfer.ActualPiConjugateKummerGenericHelpers20261017
open MazurTransfer.EquivariantNormPreimageCocycle
variable {G H : Type*} [Group G] [CommGroup H]
variable (ρ : G → H →* H) (f : H →* H)
theorem difference_in_kernel (heq : ∀ σ x, f (ρ σ x) = ρ σ (f x))
    {a b : H} (hb : f b = a) (ha : ∀ σ, ρ σ a = a) (σ : G) :
    f (difference ρ b σ) = 1 := by
  simp only [difference, map_mul, map_inv, heq, hb, ha, mul_inv_cancel]

theorem difference_cocycle (hmul : ∀ σ τ x, ρ (σ * τ) x = ρ σ (ρ τ x))
    (b : H) (σ τ : G) :
    difference ρ b (σ * τ) = difference ρ b σ * ρ σ (difference ρ b τ) := by
  simp only [difference, hmul, map_mul, map_inv]
  simp [mul_assoc, mul_left_comm, mul_comm]

theorem difference_one (hone : ∀ x, ρ 1 x = x) (b : H) :
    difference ρ b 1 = 1 := by
  simp only [difference, hone, mul_inv_cancel]
end MazurTransfer.ActualPiConjugateKummerGenericHelpers20261017
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open scoped CategoryTheory.MonObj
local instance actualPiConjugateKummerExistenceProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualPiConjugateKummerExistenceProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualPiConjugateKummerExistenceProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualPiConjugateKummerExistenceProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open MazurTransfer.Order13ActualPicardNormKummerCocycles
namespace MazurTransfer.ActualPiConjugateKummerPointHelpers20261017
variable (K : Type) [Field K] [CharZero K]
theorem difference_cocycle (b : Points K) (σ τ : K ≃ₐ[ℚ] K) :
    difference K b (σ * τ) = difference K b σ * actionHom K σ (difference K b τ) :=
  MazurTransfer.ActualPiConjugateKummerGenericHelpers20261017.difference_cocycle (actionHom K)
    (fun σ τ x => FieldAutomorphismOverPointAction.act_mul actualPicard.toBase σ τ x) b σ τ

theorem difference_one (b : Points K) : difference K b 1 = 1 :=
  MazurTransfer.ActualPiConjugateKummerGenericHelpers20261017.difference_one (actionHom K)
    (fun x => FieldAutomorphismOverPointAction.act_one actualPicard.toBase x) b

theorem difference_in_kernel
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a)
    (σ : K ≃ₐ[ℚ] K) : difference K b σ ≫ φ = 1 :=
  MazurTransfer.ActualPiConjugateKummerGenericHelpers20261017.difference_in_kernel (actionHom K) (normHom K φ)
    (fun σ x => (FieldAutomorphismOverPointAction.act_comp actualPicard.toBase σ x φ).symm)
    hb (fun σ => FieldAutomorphismOverPointAction.rationalPoint_fixed actualPicard.toBase σ a) σ
end MazurTransfer.ActualPiConjugateKummerPointHelpers20261017
open MazurTransfer.ActualPiConjugateKummerPointHelpers20261017
theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (a : RationalPoints) :
    ∃ b : Points K, b ≫ schemePiConjugate = rationalPoint K a ∧
      (∀ σ : K ≃ₐ[ℚ] K,
        difference K b σ ≫ schemePiConjugate = 1 ∧ (difference K b σ) ^ 19 = 1) ∧
      (∀ σ τ : K ≃ₐ[ℚ] K,
        difference K b (σ * τ) = difference K b σ * actionHom K σ (difference K b τ)) ∧
      difference K b 1 = 1 := by
  obtain ⟨b, hb⟩ := schemePiConjugate_geometricPoint_surjective K (rationalPoint K a)
  refine ⟨b, hb, ?_, MazurTransfer.ActualPiConjugateKummerPointHelpers20261017.difference_cocycle K b, MazurTransfer.ActualPiConjugateKummerPointHelpers20261017.difference_one K b⟩
  intro σ
  have hk := MazurTransfer.ActualPiConjugateKummerPointHelpers20261017.difference_in_kernel K schemePiConjugate a b hb σ
  exact ⟨hk, schemePiConjugate_kernel_killed_nineteen _ _ hk⟩

#print axioms solution
