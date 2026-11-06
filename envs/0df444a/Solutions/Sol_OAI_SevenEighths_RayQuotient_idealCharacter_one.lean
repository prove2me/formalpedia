-- Prove2me | solution 1 for OAI.SevenEighths.RayQuotient.idealCharacter_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:01:58.269382+00:00
-- url     : https://prove2.me/submissions/64ede7a9-cb1b-434d-a3c9-65aff3026e33

import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayQuotient
import Theorems.Thm_OAI_SevenEighths_IdealCharacter_ofResidue_one


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
    idealCharacter M H hH 1 I =
      if I = ⊥ then 0 else if IsCoprime I M then 1 else 0 :=
  IdealCharacter.ofResidue_one M I
end OAI.SevenEighths.RayQuotient
