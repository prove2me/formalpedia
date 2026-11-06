-- Prove2me | solution 1 for OAI.SevenEighths.RayQuotient.identityClass_globalUnits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:03:52.486891+00:00
-- url     : https://prove2.me/submissions/f8d40677-77a8-471c-b9b0-a14fbd421e02

import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayQuotient
import Theorems.Thm_OAI_SevenEighths_RayQuotient_toFullRay_eq_one
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_apply
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
import Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_symm
import Theorems.Thm_OAI_SevenEighths_ConductorPresentation_quotientCharacter_mk
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_bot
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_inUnitSubgroup_globalUnits_iff
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
omit [Finite (A ⧸ M)] [IsPrincipalIdealRing A] [IsDomain A] hH
namespace OAI.SevenEighths.RayQuotient
theorem _root_.solution : identityClass M (globalUnits M) = principalIdeals M := by
  ext I
  simp only [identityClass, principalIdeals, Set.mem_ofPred_eq,
    inUnitSubgroup_globalUnits_iff]
end OAI.SevenEighths.RayQuotient
