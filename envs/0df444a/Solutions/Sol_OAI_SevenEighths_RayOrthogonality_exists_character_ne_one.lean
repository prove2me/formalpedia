-- Prove2me | solution 1 for OAI.SevenEighths.RayOrthogonality.exists_character_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:00:20.596664+00:00
-- url     : https://prove2.me/submissions/036e4a18-e1f0-4a1c-a474-b4a489945954

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
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
theorem _root_.solution (H : Subgroup Rˣ) {u : Rˣ} (hu : u ∉ H) :
    ∃ χ : characters H, (χ : MulChar R ℂ) u ≠ 1 := by
  by_contra hn
  apply hu
  have hall : ∀ χ ∈ characters H, χ u = 1 := by
    intro χ hχ
    by_contra h
    exact hn ⟨⟨χ, hχ⟩, h⟩
  have hh := (MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff).mpr hall
  simpa only [characters, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply] using hh
end OAI.SevenEighths.RayOrthogonality
