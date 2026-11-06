-- Prove2me | solution 1 for OAI.SevenEighths.RayQuotient.average_idealCharacters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:08:54.424687+00:00
-- url     : https://prove2.me/submissions/0a32b748-2a39-4716-92cb-17772de36d68

import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayQuotient
import Theorems.Thm_OAI_SevenEighths_RayQuotient_classNumber_pos
import Theorems.Thm_OAI_SevenEighths_RayQuotient_toFullRay_eq_one
import Theorems.Thm_OAI_SevenEighths_RayQuotient_sum_idealCharacters
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_quotientCharacter_mk
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_bot
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_sum_idealCharacters
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_apply
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_mul
attribute [local simp] OAI.SevenEighths.CharacterTransport.pullback_symm
attribute [local simp] OAI.SevenEighths.ConductorPresentation.quotientCharacter_mk
attribute [local simp] OAI.SevenEighths.IdealCharacter.ofResidue_bot


attribute [local simp] OAI.SevenEighths.RayQuotient.toFullRay_eq_one

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)
include hH
variable [IsDomain A] [IsPrincipalIdealRing A]
namespace OAI.SevenEighths.RayQuotient
theorem _root_.solution (I : Ideal A) :
    (∑ χ : Characters M H, idealCharacter M H hH χ I) / (classNumber M H : ℂ) =
      if I ∈ identityClass M H then 1 else 0 := by
  rw [sum_idealCharacters]
  have hn : (classNumber M H : ℂ) ≠ 0 := by exact_mod_cast (classNumber_pos M H).ne'
  split_ifs <;> simp [hn]
end OAI.SevenEighths.RayQuotient
