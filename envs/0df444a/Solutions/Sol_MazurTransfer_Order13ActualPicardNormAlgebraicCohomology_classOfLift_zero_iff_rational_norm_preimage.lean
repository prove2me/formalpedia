-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormAlgebraicCohomology.classOfLift_zero_iff_rational_norm_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T22:32:18.572972+00:00
-- url     : https://prove2.me/submissions/a214705e-e7d3-4072-8d51-0bd747755768

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual norm preimages define classes in Mathlib H1
of the actual geometric norm kernel. Zero classes are precisely rational
norm images. This is algebraic group cohomology; continuity is separate.
Named downstream consumer: the rational norm quotient Kummer injection.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormAlgebraicCohomologyData
import Definitions.Def_MazurTransfer_GaloisFixedOverPointScalarExtensionData
import Theorems.Thm_MazurTransfer_Order13ActualPicardGaloisFixedPointDescent_fixed_point_descends
noncomputable section
namespace MazurTransfer.ActualNormH1ZeroScalarHelpers20261017
open CategoryTheory AlgebraicGeometry
open MazurTransfer.FieldAutomorphismOverPointAction MazurTransfer.GaloisFixedOverPointDescent
variable (F K : Type) [Field F] [Field K] [Algebra F K]

theorem scalarMap_epi : Epi (fieldBase F K) := by
  letI : Surjective (fieldBase F K) := ⟨fun y => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective (fieldBase F K)

variable {F K} {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of F))

theorem scalarExtension_injective : Function.Injective
    (fun a : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Over.mk t => scalarOverMap F K ≫ a) := by
  letI : Epi (fieldBase F K) := scalarMap_epi F K
  intro a a' h
  apply Over.OverMorphism.ext
  apply (cancel_epi (fieldBase F K)).mp
  exact congrArg Over.Hom.left h

end MazurTransfer.ActualNormH1ZeroScalarHelpers20261017
namespace MazurTransfer.ActualNormH1ZeroInvariantHelpers20261017
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

end MazurTransfer.ActualNormH1ZeroInvariantHelpers20261017
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormH1ZeroCriterionProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormH1ZeroCriterionProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormH1ZeroCriterionProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormH1ZeroCriterionProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open MazurTransfer.Order13ActualPicardNormAlgebraicCohomology
namespace MazurTransfer.ActualNormH1ZeroPointHelpers20261017
variable (K : Type) [Field K] [CharZero K]
theorem rationalPoint_injective : Function.Injective (rationalPoint K) :=
  MazurTransfer.ActualNormH1ZeroScalarHelpers20261017.scalarExtension_injective (K := K) actualPicard.toBase

end MazurTransfer.ActualNormH1ZeroPointHelpers20261017
namespace MazurTransfer.ActualNormH1ZeroCohomologyHelpers20261017
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualNormH1ZeroCohomologyKernelAction20261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ
theorem classOfLift_zero_iff_kernel_coboundary
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    classOfLift K φ a b hb = 0 ↔
      ∃ z : Kernel K φ, ∀ σ : K ≃ₐ[ℚ] K,
        actionHom K σ z.val * z.val⁻¹ = difference K b σ := by
  rw [classOfLift, groupCohomology.H1π_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := groupCohomology.isMulCoboundary₁_of_mem_coboundaries₁
      (fun σ => kernelCocycle K φ a b hb σ) h
    refine ⟨z, ?_⟩
    intro σ
    have hσ := congrArg Subtype.val (hz σ)
    change actionHom K σ z.val / z.val = difference K b σ at hσ
    simpa only [div_eq_mul_inv] using hσ
  · rintro ⟨z, hz⟩
    have h : groupCohomology.IsMulCoboundary₁ (kernelCocycle K φ a b hb) := by
      refine ⟨z, ?_⟩
      intro σ
      apply Subtype.ext
      exact (show actionHom K σ z.val / z.val = difference K b σ from
        by simpa only [div_eq_mul_inv] using hz σ)
    exact (groupCohomology.coboundariesOfIsMulCoboundary₁ h).property

theorem classOfLift_zero_iff_invariant_preimage
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    classOfLift K φ a b hb = 0 ↔
      ∃ c : Points K, c ≫ φ = rationalPoint K a ∧
        ∀ σ : K ≃ₐ[ℚ] K, actionHom K σ c = c := by
  rw [classOfLift_zero_iff_kernel_coboundary]
  exact MazurTransfer.ActualNormH1ZeroInvariantHelpers20261017.coboundary_iff_invariant_preimage
    (actionHom K) (normHom K φ) hb

end MazurTransfer.ActualNormH1ZeroCohomologyHelpers20261017
theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    (a : RationalPoints) (b : Points K) (hb : b ≫ φ = rationalPoint K a) :
    classOfLift K φ a b hb = 0 ↔ ∃ c : RationalPoints, c ≫ φ = a := by
  rw [MazurTransfer.ActualNormH1ZeroCohomologyHelpers20261017.classOfLift_zero_iff_invariant_preimage]
  constructor
  · rintro ⟨c, hc, hfixed⟩
    obtain ⟨cQ, hcQ, -⟩ := fixed_point_descends K c hfixed
    refine ⟨cQ, ?_⟩
    apply MazurTransfer.ActualNormH1ZeroPointHelpers20261017.rationalPoint_injective K
    change GaloisFixedOverPointDescent.scalarOverMap ℚ K ≫ (cQ ≫ φ) = rationalPoint K a
    rw [← Category.assoc]
    change rationalPoint K cQ ≫ φ = rationalPoint K a
    rw [hcQ]
    exact hc
  · rintro ⟨cQ, hcQ⟩
    refine ⟨rationalPoint K cQ, ?_, ?_⟩
    · change (GaloisFixedOverPointDescent.scalarOverMap ℚ K ≫ cQ) ≫ φ = rationalPoint K a
      rw [Category.assoc, hcQ]
      rfl
    · exact fun σ => FieldAutomorphismOverPointAction.rationalPoint_fixed actualPicard.toBase σ cQ

#print axioms solution
