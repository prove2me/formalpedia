-- Prove2me | solution 1 for MazurTransfer.original_unconditional_arithmetic_character_finiteness
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T23:05:07.724186+00:00
-- url     : https://prove2.me/submissions/b5ebf956-055b-4aa4-8120-eeaa7f392367

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original common finite field gives a finite-quotient injection for the same genuine arithmetic character-condition space, and the original injective embedding transfers finiteness to the same unramified reflected-character classes. No arithmetic finiteness hypothesis is assumed.
Named downstream consumer: unconditional finiteness of the original rational pi norm quotient and its subsequent numerical Selmer dimension bound.
-/
import Definitions.Def_MazurTransfer_OriginalActualKernelCharacterUniformFieldData20261019
import Definitions.Def_MazurTransfer_Order13OriginalUnramifiedKernelCharacterEmbeddingData20261019
import Theorems.Thm_MazurTransfer_original_actual_kernel_character_uniform_field_properties
import Theorems.Thm_MazurTransfer_original_character_family_finite_of_uniform_kernel
import Theorems.Thm_MazurTransfer_order13_unramified_kernel_character_embedding_injective
noncomputable section
open MazurTransfer
open CategoryTheory RepresentationDiscreteCoefficients
open Order13ActualCyclotomicThirteenKernelCharacter Order13ActualSelectedCharacterKummerKernel
open Order13ActualUnramifiedKernelCharacterEmbedding Order13ActualReflectedCharacterField Order13ActualKernelCharacterUniformLevel Order13ActualSelectedCharacterUnramifiedKernelLifts
local notation "F" => AlgebraicClosure ℚ
local notation "Γ" => F ≃ₐ[ℚ] F
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterUniformLevel.instIsGaloisRatAlgebraicClosure_order13ActualKernelCharacterUniformLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterUniformLevel.instFactPrimeOfNatNat_order13ActualKernelCharacterUniformLevel
attribute [local instance] MazurTransfer.Order13ActualKernelCharacterUniformLevel.instModuleZModOfNatNatKernelCharactersAlgebraicClosureRat_order13ActualKernelCharacterUniformLevel
namespace MazurTransfer.OriginalUnconditionalArithmeticCharacterFinitenessBoundary20261019
end MazurTransfer.OriginalUnconditionalArithmeticCharacterFinitenessBoundary20261019
namespace MazurTransfer.OriginalUnconditionalArithmeticCharacterFinitenessProof20261019
variable (z : F) (hz : IsPrimitiveRoot z 13)
local notation "χ" => piConjugateReflectedCharacter F z hz
local notation "Mχ" => Coefficient (piLineRepresentation F z hz)
local instance originalFiniteCoefficientProvider39220261019 : Finite Mχ := Finite.of_injective (fun m : Mχ => m.val) (fun _ _ h => Coefficient.ext h)
theorem kernelCharacterConditions_finite : Finite (piKernelCharacterConditions F z hz) := by
  let T := (uniformField z hz).fixingSubgroup
  haveI := MazurTransfer.original_actual_kernel_character_uniform_field_properties.1 z hz
  haveI : T.FiniteIndex := ⟨by
    change (uniformField z hz).fixingSubgroup.index ≠ 0
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'⟩
  apply MazurTransfer.original_character_family_finite_of_uniform_kernel (χ).ker T
    (MazurTransfer.original_actual_kernel_character_uniform_field_properties.2.2.2.1 z hz)
    (fun f : piKernelCharacterConditions F z hz => f.val.toMul.toMonoidHom)
  · intro f g he
    apply Subtype.ext
    apply Additive.toMul.injective
    apply ContinuousMonoidHom.ext
    intro s
    exact congrArg (fun h : (χ).ker →* Mχ => h s) he
  · exact MazurTransfer.original_actual_kernel_character_uniform_field_properties.2.2.2.2 z hz
theorem kernelCharacterConditions_finiteDimensional :
    FiniteDimensional (ZMod 19) (piKernelCharacterConditions F z hz) := by
  haveI := kernelCharacterConditions_finite z hz
  exact Module.Finite.of_finite
theorem unramifiedCharacterClasses_finiteDimensional :
    FiniteDimensional (ZMod 19) (piUnramifiedCharacterClasses F z hz) := by
  haveI := kernelCharacterConditions_finiteDimensional z hz
  exact FiniteDimensional.of_injective (piUnramifiedKernelCharacterEmbedding F z hz)
    (MazurTransfer.order13_unramified_kernel_character_embedding_injective F z hz)
theorem unramifiedCharacterClasses_finite : Finite (piUnramifiedCharacterClasses F z hz) := by
  haveI := unramifiedCharacterClasses_finiteDimensional z hz
  exact Module.finite_of_finite (ZMod 19)
end MazurTransfer.OriginalUnconditionalArithmeticCharacterFinitenessProof20261019
theorem solution : (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), Finite (piKernelCharacterConditions (AlgebraicClosure ℚ) z hz)) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), FiniteDimensional (ZMod 19) (piKernelCharacterConditions (AlgebraicClosure ℚ) z hz)) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), FiniteDimensional (ZMod 19) (piUnramifiedCharacterClasses (AlgebraicClosure ℚ) z hz)) ∧ (∀ (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z 13), Finite (piUnramifiedCharacterClasses (AlgebraicClosure ℚ) z hz)) := by
  exact ⟨MazurTransfer.OriginalUnconditionalArithmeticCharacterFinitenessProof20261019.kernelCharacterConditions_finite, MazurTransfer.OriginalUnconditionalArithmeticCharacterFinitenessProof20261019.kernelCharacterConditions_finiteDimensional, MazurTransfer.OriginalUnconditionalArithmeticCharacterFinitenessProof20261019.unramifiedCharacterClasses_finiteDimensional, MazurTransfer.OriginalUnconditionalArithmeticCharacterFinitenessProof20261019.unramifiedCharacterClasses_finite⟩
#print axioms solution
