-- Prove2me | solution 1 for OAI.SevenEighths.RayOrthogonality.principalIdeals_iff_congruent_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:00:46.66548+00:00
-- url     : https://prove2.me/submissions/1d14c59b-5fbe-4242-a32e-288dc676ba7f

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
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
variable [IsDomain A] [IsPrincipalIdealRing A]
omit [Finite (A ⧸ M)] [IsPrincipalIdealRing A]
namespace OAI.SevenEighths.RayOrthogonality
theorem _root_.solution (I : Ideal A) :
    I ∈ principalIdeals M ↔ ∃ a : A, a ≠ 0 ∧
      Ideal.span ({a} : Set A) = I ∧ Ideal.Quotient.mk M a = 1 := by
  constructor
  · rintro ⟨hI, a, ha, u, hu⟩
    refine ⟨a * (u⁻¹ : Aˣ), ?_, ?_, ?_⟩
    · apply mul_ne_zero
      · exact fun h ↦ hI (ha ▸ (Ideal.span_singleton_eq_bot.mpr h))
      · exact Units.ne_zero _
    · rw [Ideal.span_singleton_mul_right_unit (u⁻¹).isUnit, ha]
    · rw [map_mul, ← hu, ← map_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, map_one]
  · rintro ⟨a, ha, hI, hq⟩
    refine ⟨?_, a, hI, 1, ?_⟩
    · exact fun h ↦ ha (Ideal.span_singleton_eq_bot.mp (hI.trans h))
    · simpa only [Units.val_one, map_one] using hq.symm
end OAI.SevenEighths.RayOrthogonality
