-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormAlgebraicKummerInjection.classOfLift_eq_iff_rational_norm_difference
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T22:42:10.828548+00:00
-- url     : https://prove2.me/submissions/4c0c110f-97e9-468c-acbb-32249778cad0

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the rational quotient by an actual norm map injects
into Mathlib algebraic H1 of its actual geometric norm kernel.
Continuity and local conditions are separate obligations.
Named downstream consumer: continuous Kummer and Selmer bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormAlgebraicCohomologyData
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormAlgebraicCohomology_classOfLift_zero_iff_rational_norm_preimage
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualNormH1EqualityProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormH1EqualityProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualNormH1EqualityProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualNormH1EqualityProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
open Order13ActualPicardNormAlgebraicCohomology
namespace MazurTransfer.ActualNormH1EqualityDivisionHelpers20261017
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualNormH1EqualityKernelAction20261017 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ
theorem lift_div (a a' : RationalPoints) (b b' : Points K)
    (hb : b ≫ φ = rationalPoint K a) (hb' : b' ≫ φ = rationalPoint K a') :
    (b / b') ≫ φ = rationalPoint K (a / a') := by
  change normHom K φ (b / b') = rationalPointHom K (a / a')
  calc
    normHom K φ (b / b') = normHom K φ b / normHom K φ b' := map_div _ _ _
    _ = rationalPointHom K a / rationalPointHom K a' := congrArg₂ (fun x y => x / y) hb hb'
    _ = rationalPointHom K (a / a') := (map_div _ _ _).symm

theorem cocycle_div (a a' : RationalPoints) (b b' : Points K)
    (hb : b ≫ φ = rationalPoint K a) (hb' : b' ≫ φ = rationalPoint K a') :
    cocycle K φ (a / a') (b / b') (lift_div K φ a a' b b' hb hb') =
      cocycle K φ a b hb - cocycle K φ a' b' hb' := by
  apply Subtype.ext
  funext σ
  apply Subtype.ext
  change difference K (b / b') σ = difference K b σ / difference K b' σ
  simp [difference, EquivariantNormPreimageCocycle.difference, div_eq_mul_inv,
    map_mul, map_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

theorem classOfLift_div (a a' : RationalPoints) (b b' : Points K)
    (hb : b ≫ φ = rationalPoint K a) (hb' : b' ≫ φ = rationalPoint K a') :
    classOfLift K φ (a / a') (b / b') (lift_div K φ a a' b b' hb hb') =
      classOfLift K φ a b hb - classOfLift K φ a' b' hb' := by
  rw [classOfLift, cocycle_div, map_sub]
  rfl

end MazurTransfer.ActualNormH1EqualityDivisionHelpers20261017
theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] (a a' : RationalPoints) (b b' : Points K)
    (hb : b ≫ φ = rationalPoint K a) (hb' : b' ≫ φ = rationalPoint K a') :
    classOfLift K φ a b hb = classOfLift K φ a' b' hb' ↔
      ∃ c : RationalPoints, c ≫ φ = a / a' := by
  rw [← sub_eq_zero, ← MazurTransfer.ActualNormH1EqualityDivisionHelpers20261017.classOfLift_div K φ a a' b b' hb hb']
  exact classOfLift_zero_iff_rational_norm_preimage K φ _ _ _

#print axioms solution
