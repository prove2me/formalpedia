-- Prove2me | solution 1 for OAI.SevenEighths.RayQuotient.norm_idealCharacter_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:03:13.783335+00:00
-- url     : https://prove2.me/submissions/f8fc9ba2-c0b4-463d-9cfe-d7ce191327eb

import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayQuotient
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_norm_ofResidue_le_one


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
theorem _root_.solution (χ : Characters M H) (I : Ideal A) :
    ‖idealCharacter M H hH χ I‖ ≤ 1 :=
  IdealCharacter.norm_ofResidue_le_one M χ _ I
end OAI.SevenEighths.RayQuotient
