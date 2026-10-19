-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormSubgroupRestriction.restrictedClass_zero_iff_subgroup_invariant_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T00:38:12.256827+00:00
-- url     : https://prove2.me/submissions/05b1ce16-1506-4b6c-b21a-6e2010f6e457

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: restriction of actual continuous norm classes to Galois
subgroups has zero class exactly when there is a subgroup-invariant norm
preimage. Named downstream consumer: decomposition-group local conditions.
No arithmetic identification of decomposition groups is asserted here.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormSubgroupRestrictionWithCoboundaryLawDataV220261018
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: triviality of a kernel-valued preimage cocycle is
equivalent to the existence of an invariant preimage.
Named downstream consumer: the zero criterion for actual Picard norm
classes in Mathlib algebraic group cohomology.
-/
namespace MazurTransfer.ActualNormSubgroupInvariantPrivate20261018
variable {G H : Type} [Group G] [CommGroup H]
variable (ρ : G → H →* H) (f : H →* H)

theorem coboundary_iff_invariant_preimage {a b : H} (hb : f b = a) :
    (∃ z : f.ker, ∀ σ, ρ σ z.val * z.val⁻¹ = ρ σ b * b⁻¹) ↔
      ∃ c : H, f c = a ∧ ∀ σ, ρ σ c = c := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨b * z.val⁻¹, ?_, ?_⟩
    · have hz0 : f z.val = 1 := z.property
      simp only [map_mul, map_inv, hb, hz0, inv_one, mul_one]
    · intro σ
      have hσ : ρ σ b = (ρ σ z.val * z.val⁻¹) * b :=
        (mul_inv_eq_iff_eq_mul).mp (hz σ).symm
      rw [map_mul, map_inv, hσ]
      simp [mul_assoc, mul_left_comm, mul_comm]
  · rintro ⟨c, hc, hfixed⟩
    have hz : f (b * c⁻¹) = 1 := by simp only [map_mul, map_inv, hb, hc, mul_inv_cancel]
    refine ⟨⟨b * c⁻¹, hz⟩, ?_⟩
    intro σ
    simp only [map_mul, map_inv, hfixed]
    group

end MazurTransfer.ActualNormSubgroupInvariantPrivate20261018

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
local instance actualNormSubgroupInvariantSourceProvider20261018920261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormSubgroupInvariantSourceProvider202610181020261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormSubgroupInvariantSourceProvider202610181120261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormSubgroupInvariantSourceProvider202610181220261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
local instance actualNormSubgroupInvariantSourceProvider202610181320261017 (K : Type) [Field K] [CharZero K] : TopologicalSpace (Points K) := pointsTopology K
local instance actualNormSubgroupInvariantSourceProvider202610181420261017 (K : Type) [Field K] [CharZero K] : DiscreteTopology (Points K) := ⟨rfl⟩
local instance actualNormSubgroupInvariantSourceProvider202610181520261017 (K : Type) [Field K] [CharZero K] : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance actualNormSubgroupInvariantSourceProvider202610181620261017 (K : Type) [Field K] [CharZero K] (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ

open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology
open MazurTransfer.Order13ActualPicardNormContinuousCohomology

open MazurTransfer.Order13ActualPicardNormSubgroupRestriction

theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left]
    (S : Subgroup (K ≃ₐ[ℚ] K))
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    restrictNormClass K φ S (continuousClassOfLift K φ a b hb) = 0 ↔
      ∃ c : Points K, c ≫ φ = rationalPoint K a ∧ ∀ σ : S, actionHom K σ.val c = c := by
  rw [restrictedClass_zero_iff_subgroup_coboundary]
  exact MazurTransfer.ActualNormSubgroupInvariantPrivate20261018.coboundary_iff_invariant_preimage
    (fun σ : S => actionHom K σ.val) (normHom K φ) hb

#print axioms solution
