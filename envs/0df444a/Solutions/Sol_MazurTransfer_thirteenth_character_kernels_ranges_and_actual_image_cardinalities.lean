-- Prove2me | solution 1 for MazurTransfer.thirteenth_character_kernels_ranges_and_actual_image_cardinalities
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T00:48:43.9335+00:00
-- url     : https://prove2.me/submissions/bbb2e38d-2525-4688-a06a-b62712093d6c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the explicit arithmetic13 characters have image of exactly
six elements and their cyclotomic power-map kernel is exactly {1,-1}.
Named downstream consumer: the actual kernel splitting field and local
Kummer restrictions for the nineteen-norm descent.
-/
import Mathlib
import Definitions.Def_MazurTransfer_ThirteenToNineteenOriginalCharacterDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualThirteenthCyclotomicReflectedCharacterOriginalData20261018
import Theorems.Thm_MazurTransfer_thirteen_to_nineteen_character_certificates
import Theorems.Thm_MazurTransfer_thirteenth_root_galois_quotient_certificates
noncomputable section
open MazurTransfer.ThirteenToNineteenCharacters MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018
namespace MazurTransfer.ThirteenthCharacterKernelRangeImageProofHelpers20261019
theorem character_kernel (u : (ZMod 13)ˣ) :
    character u = 1 ↔ u = 1 ∨ u = generator ^ 6 := by
  have h : ∀ u : (ZMod 13)ˣ, character u = 1 ↔ u = 1 ∨ u = generator ^ 6 := by decide
  exact h u

theorem conjugateCharacter_kernel (u : (ZMod 13)ˣ) :
    conjugateCharacter u = 1 ↔ u = 1 ∨ u = generator ^ 6 := by
  change (character u)⁻¹ = 1 ↔ _
  rw [inv_eq_one]
  exact character_kernel u

theorem generator_six_coe : ((generator ^ 6 : (ZMod 13)ˣ) : ZMod 13) = (-1 : ZMod 13) := by decide

theorem range_eq_zpowers_generator (χ : (ZMod 13)ˣ →* (ZMod 19)ˣ) :
    χ.range = Subgroup.zpowers (χ generator) := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    obtain ⟨n, hn⟩ := (MazurTransfer.thirteen_to_nineteen_character_certificates).2.2.2.1 u
    rw [hn, map_pow]
    exact Subgroup.npow_mem_zpowers _ _
  · exact Subgroup.zpowers_le.mpr ⟨generator, rfl⟩

theorem character_range_card : Nat.card character.range = 6 := by
  rw [range_eq_zpowers_generator, Nat.card_zpowers, (MazurTransfer.thirteen_to_nineteen_character_certificates).2.2.2.2.1]

theorem conjugateCharacter_range_card : Nat.card conjugateCharacter.range = 6 := by
  rw [range_eq_zpowers_generator, Nat.card_zpowers, (MazurTransfer.thirteen_to_nineteen_character_certificates).2.2.2.2.2]

variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
theorem piReflectedCharacter_range (z : K) (hz : IsPrimitiveRoot z 13) :
    (piReflectedCharacter K z hz).range = character.range := by
  ext u
  change (∃ σ : K ≃ₐ[ℚ] K, character (hz.autToPow ℚ σ) = u) ↔ ∃ v, character v = u
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨_, hσ⟩
  · rintro ⟨v, hv⟩
    obtain ⟨σ, hσ⟩ := (MazurTransfer.thirteenth_root_galois_quotient_certificates).2.2.1 K z hz v
    exact ⟨σ, (congrArg character hσ).trans hv⟩

theorem piConjugateReflectedCharacter_range (z : K) (hz : IsPrimitiveRoot z 13) :
    (piConjugateReflectedCharacter K z hz).range = conjugateCharacter.range := by
  ext u
  change (∃ σ : K ≃ₐ[ℚ] K, conjugateCharacter (hz.autToPow ℚ σ) = u) ↔ ∃ v, conjugateCharacter v = u
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨_, hσ⟩
  · rintro ⟨v, hv⟩
    obtain ⟨σ, hσ⟩ := (MazurTransfer.thirteenth_root_galois_quotient_certificates).2.2.1 K z hz v
    exact ⟨σ, (congrArg conjugateCharacter hσ).trans hv⟩

theorem piReflectedCharacter_image_card_six (z : K) (hz : IsPrimitiveRoot z 13) :
    Nat.card (piReflectedCharacter K z hz).range = 6 := by
  rw [piReflectedCharacter_range K z hz, character_range_card]

theorem piConjugateReflectedCharacter_image_card_six (z : K) (hz : IsPrimitiveRoot z 13) :
    Nat.card (piConjugateReflectedCharacter K z hz).range = 6 := by
  rw [piConjugateReflectedCharacter_range K z hz, conjugateCharacter_range_card]

end MazurTransfer.ThirteenthCharacterKernelRangeImageProofHelpers20261019
theorem solution :
    (∀  (u : (ZMod 13)ˣ) ,
    character u = 1 ↔ u = 1 ∨ u = generator ^ 6) ∧
    (∀  (u : (ZMod 13)ˣ) ,
    conjugateCharacter u = 1 ↔ u = 1 ∨ u = generator ^ 6) ∧
    (((generator ^ 6 : (ZMod 13)ˣ) : ZMod 13) = (-1 : ZMod 13)) ∧
    (∀  (χ : (ZMod 13)ˣ →* (ZMod 19)ˣ) ,
    χ.range = Subgroup.zpowers (χ generator)) ∧
    (Nat.card character.range = 6) ∧
    (Nat.card conjugateCharacter.range = 6) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : K) (hz : IsPrimitiveRoot z 13) ,
    (piReflectedCharacter K z hz).range = character.range) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : K) (hz : IsPrimitiveRoot z 13) ,
    (piConjugateReflectedCharacter K z hz).range = conjugateCharacter.range) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : K) (hz : IsPrimitiveRoot z 13) ,
    Nat.card (piReflectedCharacter K z hz).range = 6) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] (z : K) (hz : IsPrimitiveRoot z 13) ,
    Nat.card (piConjugateReflectedCharacter K z hz).range = 6) := by
  exact ⟨MazurTransfer.ThirteenthCharacterKernelRangeImageProofHelpers20261019.character_kernel, MazurTransfer.ThirteenthCharacterKernelRangeImageProofHelpers20261019.conjugateCharacter_kernel, MazurTransfer.ThirteenthCharacterKernelRangeImageProofHelpers20261019.generator_six_coe, MazurTransfer.ThirteenthCharacterKernelRangeImageProofHelpers20261019.range_eq_zpowers_generator, MazurTransfer.ThirteenthCharacterKernelRangeImageProofHelpers20261019.character_range_card, MazurTransfer.ThirteenthCharacterKernelRangeImageProofHelpers20261019.conjugateCharacter_range_card, MazurTransfer.ThirteenthCharacterKernelRangeImageProofHelpers20261019.piReflectedCharacter_range, MazurTransfer.ThirteenthCharacterKernelRangeImageProofHelpers20261019.piConjugateReflectedCharacter_range, MazurTransfer.ThirteenthCharacterKernelRangeImageProofHelpers20261019.piReflectedCharacter_image_card_six, MazurTransfer.ThirteenthCharacterKernelRangeImageProofHelpers20261019.piConjugateReflectedCharacter_image_card_six⟩
#print axioms solution
