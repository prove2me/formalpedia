-- Prove2me | solution 1 for OAI.SevenEighths.RayOrthogonality.sum_characters_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:01:25.873989+00:00
-- url     : https://prove2.me/submissions/b232b011-20fc-4651-b394-58cc690c1703

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_card_characters
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_exists_character_ne_one
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_quotientCharacter_mk
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_bot
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_apply
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_mul
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_symm
attribute [local simp] OAI.SevenEighths.ConductorPresentation.quotientCharacter_mk
attribute [local simp] OAI.SevenEighths.IdealCharacter.ofResidue_bot



set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {R : Type*} [CommMonoid R] [Finite R]
namespace OAI.SevenEighths.RayOrthogonality
theorem _root_.solution (H : Subgroup Rˣ) (u : Rˣ) :
    ∑ χ : characters H, (χ : MulChar R ℂ) u =
      if u ∈ H then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by
  by_cases hu : u ∈ H
  · simp only [hu, ite_true]
    calc
      _ = ∑ _χ : characters H, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro χ _
        exact (mem_characters_iff H χ).mp χ.property u hu
      _ = _ := by simp [card_characters]
  · simp only [hu, ite_false]
    obtain ⟨χ, hχ⟩ := exists_character_ne_one H hu
    refine eq_zero_of_mul_eq_self_left hχ ?_
    simp only [Finset.mul_sum, ← MulChar.mul_apply]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl
end OAI.SevenEighths.RayOrthogonality
