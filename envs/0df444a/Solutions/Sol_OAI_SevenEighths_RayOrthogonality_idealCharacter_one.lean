-- Prove2me | solution 1 for OAI.SevenEighths.RayOrthogonality.idealCharacter_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:00:46.132714+00:00
-- url     : https://prove2.me/submissions/9cb9ee9f-a79a-4efb-8a50-b0b83e5a24db

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_one


set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
variable [IsDomain A] [IsPrincipalIdealRing A]
namespace OAI.SevenEighths.RayOrthogonality
theorem _root_.solution (I : Ideal A) :
    idealCharacter M 1 I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 :=
  IdealCharacter.ofResidue_one M I
end OAI.SevenEighths.RayOrthogonality
