-- Prove2me | solution 1 for OAI.SevenEighths.RayOrthogonality.sum_idealCharacters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:04:06.707461+00:00
-- url     : https://prove2.me/submissions/ca00f5dc-77f1-48c1-bcdf-cebef8ce2c25

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_sum_rayCharacters
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_principalIdeals_iff_generator
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_quotientCharacter_mk
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_bot
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_of_generator
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
namespace OAI.SevenEighths.RayOrthogonality
theorem _root_.solution (I : Ideal A) :
    ∑ χ : rayCharacters M, idealCharacter M χ I =
      if I ∈ principalIdeals M then (rayCard M : ℂ) else 0 := by
  by_cases hI : I = ⊥
  · subst I
    simp [idealCharacter, principalIdeals]
  · have heq (χ : rayCharacters M) : idealCharacter M χ I =
        (χ : MulChar (A ⧸ M) ℂ) (Ideal.Quotient.mk M (Submodule.IsPrincipal.generator I)) := by
      exact IdealCharacter.ofResidue_of_generator M χ _ hI (Ideal.span_singleton_generator I)
    simp only [heq, sum_rayCharacters, principalIdeals_iff_generator M hI]
end OAI.SevenEighths.RayOrthogonality
