-- Prove2me | solution 1 for MazurTransfer.original_actual_reflected_character_field_and_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T20:50:25.376277+00:00
-- url     : https://prove2.me/submissions/c2919ed0-28bb-41da-8543-2b0f10e56148

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same actual reflected coefficient character is trivialized by the original explicit degree-six field, with exact fixing-subgroup equality and injective original continuous H1 restriction.
Named downstream consumer: the genuine kernel characters and their uniform finite arithmetic level.
-/
import Definitions.Def_MazurTransfer_OriginalActualReflectedCharacterFieldData20261019
import Theorems.Thm_MazurTransfer_original_thirteenth_character_real_field_and_degree
import Theorems.Thm_MazurTransfer_original_continuous_scalar_character_kernel_restriction_injective
noncomputable section
open MazurTransfer
open RepresentationDiscreteCoefficients ScalarCharacterLine
open Order13ActualCyclotomicThirteenKernelCharacter Order13ActualSelectedCharacterKummerKernel
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologySubgroupRestriction
open ThirteenCharacterRealField
local notation "F" => AlgebraicClosure ℚ
open Order13ActualReflectedCharacterField
attribute [local instance] MazurTransfer.Order13ActualReflectedCharacterField.instIsGaloisRatAlgebraicClosure_order13ActualReflectedCharacterField
attribute [local instance] MazurTransfer.Order13ActualReflectedCharacterField.instFactPrimeOfNatNat_order13ActualReflectedCharacterField
namespace MazurTransfer.OriginalActualReflectedCharacterFieldProofBoundary20261019
end MazurTransfer.OriginalActualReflectedCharacterFieldProofBoundary20261019
namespace MazurTransfer.OriginalActualReflectedCharacterFieldProof20261019
variable (z : F) (hz : IsPrimitiveRoot z 13)
theorem reflectedField_finiteDimensional : FiniteDimensional ℚ (reflectedField z) :=
  MazurTransfer.original_thirteenth_character_real_field_and_degree.2.2.2.2.2.2.1 z
theorem reflectedField_fixingSubgroup : (reflectedField z).fixingSubgroup =
    (piConjugateReflectedCharacter F z hz).ker :=
  MazurTransfer.original_thirteenth_character_real_field_and_degree.2.2.2.2.2.2.2.2.1 z hz
include hz in
theorem reflectedField_finrank : Module.finrank ℚ (reflectedField z) = 6 :=
  MazurTransfer.original_thirteenth_character_real_field_and_degree.2.2.2.2.2.2.2.2.2.2.2 z hz
include hz in
theorem reflectedField_isGalois : IsGalois ℚ (reflectedField z) :=
  MazurTransfer.original_thirteenth_character_real_field_and_degree.2.2.2.2.2.2.2.2.2.2.1 z hz
theorem reflectedField_coefficient_action_trivial (s : (reflectedField z).fixingSubgroup)
    (m : Coefficient (piLineRepresentation F z hz)) : s • m = m := by
  apply Coefficient.ext
  change (piConjugateReflectedCharacter F z hz s.val : ZMod 19) * m.val = m.val
  have hs : piConjugateReflectedCharacter F z hz s.val = 1 := by
    exact (le_of_eq (reflectedField_fixingSubgroup z hz)) s.property
  rw [hs, Units.val_one, one_mul]
theorem reflectedField_H1_restriction_injective : Function.Injective
    (restriction (F ≃ₐ[ℚ] F) (Coefficient (piLineRepresentation F z hz))
      (reflectedField z).fixingSubgroup) := by
  rw [reflectedField_fixingSubgroup z hz]
  exact MazurTransfer.original_continuous_scalar_character_kernel_restriction_injective.2.2.2.2
    (piConjugateReflectedCharacter F z hz)
end MazurTransfer.OriginalActualReflectedCharacterFieldProof20261019
theorem solution : (∀ (z : AlgebraicClosure ℚ), FiniteDimensional ℚ (reflectedField z)) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), (reflectedField z).fixingSubgroup = (piConjugateReflectedCharacter (AlgebraicClosure ℚ) z hz).ker) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), Module.finrank ℚ (reflectedField z) = 6) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), IsGalois ℚ (reflectedField z)) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), ∀ (s : (reflectedField z).fixingSubgroup) (m : Coefficient (piLineRepresentation (AlgebraicClosure ℚ) z hz)), s • m = m) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), Function.Injective (restriction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Coefficient (piLineRepresentation (AlgebraicClosure ℚ) z hz)) (reflectedField z).fixingSubgroup)) := by
  exact ⟨MazurTransfer.OriginalActualReflectedCharacterFieldProof20261019.reflectedField_finiteDimensional, MazurTransfer.OriginalActualReflectedCharacterFieldProof20261019.reflectedField_fixingSubgroup, MazurTransfer.OriginalActualReflectedCharacterFieldProof20261019.reflectedField_finrank, MazurTransfer.OriginalActualReflectedCharacterFieldProof20261019.reflectedField_isGalois, MazurTransfer.OriginalActualReflectedCharacterFieldProof20261019.reflectedField_coefficient_action_trivial, MazurTransfer.OriginalActualReflectedCharacterFieldProof20261019.reflectedField_H1_restriction_injective⟩
#print axioms solution
