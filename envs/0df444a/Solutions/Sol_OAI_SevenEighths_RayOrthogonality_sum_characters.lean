-- Prove2me | solution 1 for OAI.SevenEighths.RayOrthogonality.sum_characters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:02:22.436931+00:00
-- url     : https://prove2.me/submissions/6df59301-167c-4008-96e8-222944bf0e3c

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_sum_characters_unit
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
theorem _root_.solution (H : Subgroup Rˣ) (r : R) :
    ∑ χ : characters H, (χ : MulChar R ℂ) r =
      if inUnitSubgroup H r then (Nat.card (Rˣ ⧸ H) : ℂ) else 0 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    have hi : inUnitSubgroup H (u : R) ↔ u ∈ H := by
      constructor
      · rintro ⟨v, hv, h⟩
        exact (Units.ext hv) ▸ h
      · exact fun h ↦ ⟨u, rfl, h⟩
    rw [sum_characters_unit, hi]
  · have hn : ¬ inUnitSubgroup H r := by
      rintro ⟨u, rfl, _⟩
      exact hr u.isUnit
    simp only [hn, ite_false]
    exact Finset.sum_eq_zero fun χ _ ↦ MulChar.map_nonunit χ.val hr
end OAI.SevenEighths.RayOrthogonality
