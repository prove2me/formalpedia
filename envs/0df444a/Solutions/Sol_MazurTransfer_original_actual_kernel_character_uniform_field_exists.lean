-- Prove2me | solution 1 for MazurTransfer.original_actual_kernel_character_uniform_field_exists
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T22:23:25.325382+00:00
-- url     : https://prove2.me/submissions/33023283-a78b-4475-976a-5dc0990ae6e4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: obtain one actual finite field level killing every character in the same arithmetic kernel-character condition space, using the exact original official FLT uniform-character theorem. No finiteness of that family is assumed.
Named downstream consumer: unconditional finiteness of the original arithmetic reflected-character classes.
-/
import Definitions.Def_MazurTransfer_OriginalActualKernelCharacterFiniteLevelData20261019
import Theorems.Thm_MazurTransfer_original_actual_reflected_character_field_and_restriction
import Theorems.Thm_MazurTransfer_original_actual_kernel_character_finite_level_and_inertia
import Theorems.Thm_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside
noncomputable section
open MazurTransfer
open CategoryTheory RepresentationDiscreteCoefficients
open Order13ActualCyclotomicThirteenKernelCharacter Order13ActualSelectedCharacterKummerKernel
open Order13ActualUnramifiedKernelCharacterEmbedding Order13ActualReflectedCharacterField Order13ActualKernelCharacterFiniteLevel
local notation "F" => AlgebraicClosure ℚ
local notation "Γ" => F ≃ₐ[ℚ] F
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instIsGaloisRatAlgebraicClosure_order13ActualKernelCharacterFiniteLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instFactPrimeOfNatNat_order13ActualKernelCharacterFiniteLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instModuleZModOfNatNatKernelCharactersAlgebraicClosureRat_order13ActualKernelCharacterFiniteLevel
namespace MazurTransfer.OriginalActualKernelCharacterUniformFieldExistenceBoundary20261019
end MazurTransfer.OriginalActualKernelCharacterUniformFieldExistenceBoundary20261019
namespace MazurTransfer.OriginalActualKernelCharacterUniformFieldExistenceProof20261019
variable (z : F) (hz : IsPrimitiveRoot z 13)
theorem exists_uniform_field :
    ∃ L : IntermediateField ℚ F, FiniteDimensional ℚ L ∧ reflectedField z ≤ L ∧
      ∀ (f : piKernelCharacterConditions F z hz) (σ : Γ), σ ∈ L.fixingSubgroup →
        extendedValue z hz f.val σ = 0 := by
  haveI := MazurTransfer.original_actual_reflected_character_field_and_restriction.1 z
  haveI : NumberField (reflectedField z) := ⟨⟩
  obtain ⟨L, hL, hKL, hkill⟩ := AlgebraicClosure.exists_uniform_level_of_characters_unramified_outside
    (reflectedField z) 19 (by decide) ({13, 19} : Finset ℕ)
  refine ⟨L, hL, hKL, fun f => hkill (extendedValue z hz f.val) ?_ ?_ ?_⟩
  · exact MazurTransfer.original_actual_kernel_character_finite_level_and_inertia.2.1 z hz f.val
  · exact MazurTransfer.original_actual_kernel_character_finite_level_and_inertia.2.2.2.1 z hz f.val
  · exact MazurTransfer.original_actual_kernel_character_finite_level_and_inertia.2.2.2.2 z hz f
end MazurTransfer.OriginalActualKernelCharacterUniformFieldExistenceProof20261019
theorem solution : ∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧ reflectedField z ≤ L ∧ ∀ (f : piKernelCharacterConditions (AlgebraicClosure ℚ) z hz) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), σ ∈ L.fixingSubgroup → extendedValue z hz f.val σ = 0 := by
  exact MazurTransfer.OriginalActualKernelCharacterUniformFieldExistenceProof20261019.exists_uniform_field
#print axioms solution
