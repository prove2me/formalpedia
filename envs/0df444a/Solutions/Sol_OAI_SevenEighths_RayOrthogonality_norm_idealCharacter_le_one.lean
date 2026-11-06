-- Prove2me | solution 1 for OAI.SevenEighths.RayOrthogonality.norm_idealCharacter_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:02:03.484312+00:00
-- url     : https://prove2.me/submissions/d3b25fa6-6f56-45b0-8917-f06f159f43dc

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_norm_ofResidue_le_one


set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
variable [IsDomain A] [IsPrincipalIdealRing A]
namespace OAI.SevenEighths.RayOrthogonality
theorem _root_.solution (χ : rayCharacters M) (I : Ideal A) :
    ‖idealCharacter M χ I‖ ≤ 1 := IdealCharacter.norm_ofResidue_le_one M χ _ I
end OAI.SevenEighths.RayOrthogonality
