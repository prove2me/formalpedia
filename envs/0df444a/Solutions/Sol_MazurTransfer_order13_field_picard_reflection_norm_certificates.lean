-- Prove2me | solution 1 for MazurTransfer.order13_field_picard_reflection_norm_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T21:29:45.918486+00:00
-- url     : https://prove2.me/submissions/d2fb6a5d-fce6-4653-84ec-6b53a838f7b9

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the original Anthropic FLT Picard action at
6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: exact original universal reflection identities for both
nineteen-norm maps on arithmetic Pic0.
Named downstream consumer: Order13ActualNineteenTorsionReflection.actualReflection_normPi.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13FieldPicardReflectionOriginalAdditiveEquivalenceDataAndCertificate20261018
import Definitions.Def_MazurTransfer_Order13FieldPicardCyclotomicNormData
import Theorems.Thm_MazurTransfer_Order13ActualReflectionDiamondRelation_reflectionAlgEquiv_conjugates_diamond
noncomputable section
universe u
namespace MazurTransfer.FieldPicardReflectionNormProofHelpers20261018
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ReflectionParameter Order13ActualReflectionFunctionField Order13ActualReflectionDiamondRelation
open ReflectionPicardConstructorProofHelpers20261018
open Order13FieldDiamondFunctionFieldAutomorphism Order13FieldDiamondPicardEndomorphisms
open Order13FieldPicardCyclotomicNorm Order13FieldPicardReflection
variable (K : Type u) [Field K] [CharZero K]
local instance fieldPicardReflectionNormOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance fieldPicardReflectionNormOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance fieldPicardReflectionNormOriginalCharZeroProvider20261018 : CharZero (actualCurveFunctionField K) := Algebra.charZero_of_charZero K _
theorem diamond_inverse_apply (c : ActualPicard K) :
    (diamondAlgEquiv K)⁻¹ • c = c - rho K c := by
  have h := rho_square_apply K c
  change diamondAlgEquiv K • (diamondAlgEquiv K • c) = diamondAlgEquiv K • c - c at h
  have h' := congrArg (fun z : ActualPicard K => (diamondAlgEquiv K)⁻¹ • z) h
  simp only [smul_sub, inv_smul_smul] at h'
  change (diamondAlgEquiv K)⁻¹ • c = c - diamondAlgEquiv K • c
  apply eq_sub_iff_add_eq.mpr
  rw [h']
  abel

theorem reflection_rho (a : ReflectionParameter K) (c : ActualPicard K) :
    reflection K a (rho K c) = reflection K a c - rho K (reflection K a c) := by
  have h : reflectionAlgEquiv K a * diamondAlgEquiv K =
      (diamondAlgEquiv K)⁻¹ * reflectionAlgEquiv K a := by
    have h := congrArg (fun f => f * reflectionAlgEquiv K a)
      (reflectionAlgEquiv_conjugates_diamond K a)
    simpa only [mul_assoc, reflectionAlgEquiv_square K a, mul_one] using h
  change reflectionAlgEquiv K a • (diamondAlgEquiv K • c) = _
  rw [← mul_smul, h, mul_smul, diamond_inverse_apply K]
  rfl

theorem reflection_pi (a : ReflectionParameter K) (c : ActualPicard K) :
    reflection K a (pi K c) = piConjugate K (reflection K a c) := by
  change reflection K a ((3 : ℕ) • c + (2 : ℕ) • rho K c) =
    (5 : ℕ) • reflection K a c - (2 : ℕ) • rho K (reflection K a c)
  rw [map_add, map_nsmul, map_nsmul, reflection_rho K]
  abel

theorem reflection_piConjugate (a : ReflectionParameter K) (c : ActualPicard K) :
    reflection K a (piConjugate K c) = pi K (reflection K a c) := by
  change reflection K a ((5 : ℕ) • c - (2 : ℕ) • rho K c) =
    (3 : ℕ) • reflection K a c + (2 : ℕ) • rho K (reflection K a c)
  rw [map_sub, map_nsmul, map_nsmul, reflection_rho K]
  abel

end MazurTransfer.FieldPicardReflectionNormProofHelpers20261018

open MazurTransfer.Order13ReflectionParameter MazurTransfer.Order13FieldPicardReflection
open MazurTransfer.Order13FieldDiamondPicardEndomorphisms
theorem solution :
    (∀ (K : Type u) [Field K] [CharZero K] (a : ReflectionParameter K) (c : ActualPicard K),
    reflection K a (pi K c) = piConjugate K (reflection K a c)) ∧
    (∀ (K : Type u) [Field K] [CharZero K] (a : ReflectionParameter K) (c : ActualPicard K),
    reflection K a (piConjugate K c) = pi K (reflection K a c)) := by
  exact ⟨MazurTransfer.FieldPicardReflectionNormProofHelpers20261018.reflection_pi,
    MazurTransfer.FieldPicardReflectionNormProofHelpers20261018.reflection_piConjugate⟩
#print axioms solution
