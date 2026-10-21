-- Prove2me | solution 1 for MazurTransfer.original_actual_kernel_character_finite_level_and_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T22:07:21.072409+00:00
-- url     : https://prove2.me/submissions/b2ae2b56-411b-4cf2-841b-a0a6d15c4f6d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual extended scalar character has the complete original subgroup homomorphism, genuine finite-field-level and valuation inertia properties.
Named downstream consumer: the exact official uniform-character theorem for the same actual reflected-character field.
-/
import Definitions.Def_MazurTransfer_OriginalActualKernelCharacterFiniteLevelData20261019
import Theorems.Thm_MazurTransfer_original_actual_reflected_character_field_and_restriction
import Theorems.Thm_MazurTransfer_original_continuous_character_finite_field_level
noncomputable section
open MazurTransfer
open CategoryTheory RepresentationDiscreteCoefficients
open Order13ActualCyclotomicThirteenKernelCharacter Order13ActualSelectedCharacterKummerKernel
open Order13ActualUnramifiedKernelCharacterEmbedding Order13ActualReflectedCharacterField
local notation "F" => AlgebraicClosure ℚ
local notation "Γ" => F ≃ₐ[ℚ] F
open Order13ActualKernelCharacterFiniteLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instIsGaloisRatAlgebraicClosure_order13ActualKernelCharacterFiniteLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instFactPrimeOfNatNat_order13ActualKernelCharacterFiniteLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instModuleZModOfNatNatKernelCharactersAlgebraicClosureRat_order13ActualKernelCharacterFiniteLevel
namespace MazurTransfer.OriginalActualKernelCharacterFiniteLevelProofBoundary20261019
end MazurTransfer.OriginalActualKernelCharacterFiniteLevelProofBoundary20261019
namespace MazurTransfer.OriginalActualKernelCharacterFiniteLevelProof20261019
variable (z : F) (hz : IsPrimitiveRoot z 13)
local notation "χ" => piConjugateReflectedCharacter F z hz
local notation "Mχ" => Coefficient (piLineRepresentation F z hz)
theorem extendedValue_of_mem (f : KernelCharacters F z hz) (σ : Γ) (hσ : σ ∈ (χ).ker) :
    extendedValue z hz f σ = evaluation F z hz ⟨σ, hσ⟩ f := dif_pos hσ
theorem extendedValue_hom (f : KernelCharacters F z hz) (σ τ : Γ)
    (hσ : σ ∈ (reflectedField z).fixingSubgroup) (hτ : τ ∈ (reflectedField z).fixingSubgroup) :
    extendedValue z hz f (σ * τ) = extendedValue z hz f σ + extendedValue z hz f τ := by
  have hs : σ ∈ (χ).ker := (le_of_eq (MazurTransfer.original_actual_reflected_character_field_and_restriction.2.1 z hz)) hσ
  have ht : τ ∈ (χ).ker := (le_of_eq (MazurTransfer.original_actual_reflected_character_field_and_restriction.2.1 z hz)) hτ
  rw [extendedValue_of_mem z hz f (σ * τ) ((χ).ker.mul_mem hs ht),
    extendedValue_of_mem z hz f σ hs, extendedValue_of_mem z hz f τ ht]
  change (f.toMul ((⟨σ, hs⟩ : (χ).ker) * ⟨τ, ht⟩)).val = (f.toMul ⟨σ, hs⟩).val + (f.toMul ⟨τ, ht⟩).val
  rw [map_mul f.toMul]
  rfl
theorem character_kernel_isOpen : IsOpen ((χ).ker : Set Γ) := by
  haveI := MazurTransfer.original_actual_reflected_character_field_and_restriction.1 z
  have h := IntermediateField.fixingSubgroup_isOpen (reflectedField z)
  simpa only [MazurTransfer.original_actual_reflected_character_field_and_restriction.2.1 z hz] using h
theorem extendedValue_has_finite_level (f : KernelCharacters F z hz) :
    ∃ L : IntermediateField ℚ F, FiniteDimensional ℚ L ∧
      ∀ σ ∈ L.fixingSubgroup, extendedValue z hz f σ = 0 := by
  obtain ⟨L, hL, hkill⟩ := MazurTransfer.original_continuous_character_finite_field_level.2.2.2
    F Mχ (χ).ker f.toMul (character_kernel_isOpen z hz)
  refine ⟨L, hL, fun σ hσ => ?_⟩
  obtain ⟨hs, he⟩ := hkill σ hσ
  rw [extendedValue_of_mem z hz f σ hs]
  exact congrArg Coefficient.val he
theorem extendedValue_unramified (f : piKernelCharacterConditions F z hz)
    (q : ℕ) (hq : q.Prime) (hnot : q ∉ ({13, 19} : Finset ℕ))
    (A : ValuationSubring F) (hA : A.LiesOverPrime q) (σ : Γ)
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (hfix : σ ∈ (reflectedField z).fixingSubgroup) :
    extendedValue z hz f.val σ = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h13 : q ≠ 13 := fun he => hnot (by simp [he])
  have h19 : q ≠ 19 := fun he => hnot (by simp [he])
  have hs : σ ∈ (χ).ker := (le_of_eq (MazurTransfer.original_actual_reflected_character_field_and_restriction.2.1 z hz)) hfix
  rw [extendedValue_of_mem z hz f.val σ hs]
  exact f.property.2 q h13 h19 A hA ⟨σ, hs⟩ hσ
end MazurTransfer.OriginalActualKernelCharacterFiniteLevelProof20261019
theorem solution : (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13) (f : KernelCharacters (AlgebraicClosure ℚ) z hz) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : σ ∈ (piConjugateReflectedCharacter (AlgebraicClosure ℚ) z hz).ker), extendedValue z hz f σ = evaluation (AlgebraicClosure ℚ) z hz ⟨σ, hσ⟩ f) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13) (f : KernelCharacters (AlgebraicClosure ℚ) z hz) (σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : σ ∈ (reflectedField z).fixingSubgroup) (hτ : τ ∈ (reflectedField z).fixingSubgroup), extendedValue z hz f (σ * τ) = extendedValue z hz f σ + extendedValue z hz f τ) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), IsOpen ((piConjugateReflectedCharacter (AlgebraicClosure ℚ) z hz).ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13) (f : KernelCharacters (AlgebraicClosure ℚ) z hz), ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧ ∀ σ ∈ L.fixingSubgroup, extendedValue z hz f σ = 0) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13) (f : piKernelCharacterConditions (AlgebraicClosure ℚ) z hz) (q : ℕ) (hq : q.Prime) (hnot : q ∉ ({13, 19} : Finset ℕ)) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (hfix : σ ∈ (reflectedField z).fixingSubgroup), extendedValue z hz f.val σ = 0) := by
  exact ⟨MazurTransfer.OriginalActualKernelCharacterFiniteLevelProof20261019.extendedValue_of_mem, MazurTransfer.OriginalActualKernelCharacterFiniteLevelProof20261019.extendedValue_hom, MazurTransfer.OriginalActualKernelCharacterFiniteLevelProof20261019.character_kernel_isOpen, MazurTransfer.OriginalActualKernelCharacterFiniteLevelProof20261019.extendedValue_has_finite_level, MazurTransfer.OriginalActualKernelCharacterFiniteLevelProof20261019.extendedValue_unramified⟩
#print axioms solution
