-- Prove2me | solution 1 for MazurTransfer.original_actual_kernel_character_uniform_field_properties
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T22:44:02.338403+00:00
-- url     : https://prove2.me/submissions/f87c7a90-4a0c-4574-8321-f4e52e3fbf90

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original chosen common finite field contains the original reflected field and kills every genuine arithmetic kernel character.
Named downstream consumer: unconditional finiteness of the same arithmetic character conditions.
-/
import Definitions.Def_MazurTransfer_OriginalActualKernelCharacterUniformFieldData20261019
import Theorems.Thm_MazurTransfer_original_actual_reflected_character_field_and_restriction
import Theorems.Thm_MazurTransfer_original_actual_kernel_character_finite_level_and_inertia
noncomputable section
open MazurTransfer
open CategoryTheory RepresentationDiscreteCoefficients
open Order13ActualCyclotomicThirteenKernelCharacter Order13ActualSelectedCharacterKummerKernel
open Order13ActualUnramifiedKernelCharacterEmbedding Order13ActualReflectedCharacterField Order13ActualKernelCharacterFiniteLevel
local notation "F" => AlgebraicClosure ℚ
local notation "Γ" => F ≃ₐ[ℚ] F
open Order13ActualKernelCharacterUniformLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterUniformLevel.instIsGaloisRatAlgebraicClosure_order13ActualKernelCharacterUniformLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterUniformLevel.instFactPrimeOfNatNat_order13ActualKernelCharacterUniformLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterUniformLevel.instModuleZModOfNatNatKernelCharactersAlgebraicClosureRat_order13ActualKernelCharacterUniformLevel
namespace MazurTransfer.OriginalActualKernelCharacterUniformFieldPropertiesBoundary20261019
end MazurTransfer.OriginalActualKernelCharacterUniformFieldPropertiesBoundary20261019
namespace MazurTransfer.OriginalActualKernelCharacterUniformFieldPropertiesProof20261019
variable (z : F) (hz : IsPrimitiveRoot z 13)
local notation "χ" => piConjugateReflectedCharacter F z hz
theorem uniformField_finiteDimensional : FiniteDimensional ℚ (uniformField z hz) :=
  (Classical.choose_spec (MazurTransfer.original_actual_kernel_character_uniform_field_exists z hz)).1
theorem reflectedField_le_uniformField : reflectedField z ≤ uniformField z hz :=
  (Classical.choose_spec (MazurTransfer.original_actual_kernel_character_uniform_field_exists z hz)).2.1
theorem uniformField_kills_extendedValue (f : piKernelCharacterConditions F z hz) (σ : Γ)
    (hσ : σ ∈ (uniformField z hz).fixingSubgroup) : extendedValue z hz f.val σ = 0 :=
  (Classical.choose_spec (MazurTransfer.original_actual_kernel_character_uniform_field_exists z hz)).2.2 f σ hσ
theorem uniformField_fixing_le_characterKernel :
    (uniformField z hz).fixingSubgroup ≤ (χ).ker :=
  (IntermediateField.fixingSubgroup_le (reflectedField_le_uniformField z hz)).trans
    (le_of_eq (MazurTransfer.original_actual_reflected_character_field_and_restriction.2.1 z hz))
theorem uniformField_kills_character (f : piKernelCharacterConditions F z hz)
    (t : (uniformField z hz).fixingSubgroup) :
    f.val.toMul ⟨t.val, uniformField_fixing_le_characterKernel z hz t.property⟩ = 1 := by
  apply Coefficient.ext
  have h := uniformField_kills_extendedValue z hz f t.val t.property
  rw [MazurTransfer.original_actual_kernel_character_finite_level_and_inertia.1 z hz f.val t.val (uniformField_fixing_le_characterKernel z hz t.property)] at h
  exact h
end MazurTransfer.OriginalActualKernelCharacterUniformFieldPropertiesProof20261019
theorem solution : (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), FiniteDimensional ℚ (uniformField z hz)) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), reflectedField z ≤ uniformField z hz) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13) (f : piKernelCharacterConditions (AlgebraicClosure ℚ) z hz) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : σ ∈ (uniformField z hz).fixingSubgroup), extendedValue z hz f.val σ = 0) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), (uniformField z hz).fixingSubgroup ≤ (piConjugateReflectedCharacter (AlgebraicClosure ℚ) z hz).ker) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13) (f : piKernelCharacterConditions (AlgebraicClosure ℚ) z hz) (t : (uniformField z hz).fixingSubgroup), f.val.toMul ⟨t.val, ((IntermediateField.fixingSubgroup_le ((Classical.choose_spec (MazurTransfer.original_actual_kernel_character_uniform_field_exists z hz)).2.1)).trans (le_of_eq (MazurTransfer.original_actual_reflected_character_field_and_restriction.2.1 z hz))) t.property⟩ = 1) := by
  exact ⟨MazurTransfer.OriginalActualKernelCharacterUniformFieldPropertiesProof20261019.uniformField_finiteDimensional, MazurTransfer.OriginalActualKernelCharacterUniformFieldPropertiesProof20261019.reflectedField_le_uniformField, MazurTransfer.OriginalActualKernelCharacterUniformFieldPropertiesProof20261019.uniformField_kills_extendedValue, MazurTransfer.OriginalActualKernelCharacterUniformFieldPropertiesProof20261019.uniformField_fixing_le_characterKernel, MazurTransfer.OriginalActualKernelCharacterUniformFieldPropertiesProof20261019.uniformField_kills_character⟩
#print axioms solution
