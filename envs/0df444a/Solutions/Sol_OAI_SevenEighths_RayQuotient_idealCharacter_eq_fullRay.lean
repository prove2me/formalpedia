-- Prove2me | solution 1 for OAI.SevenEighths.RayQuotient.idealCharacter_eq_fullRay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:01:03.675205+00:00
-- url     : https://prove2.me/submissions/7681fbe3-66ad-4c4b-85f9-1a8848f0c7f8

import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayQuotient

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
theorem _root_.solution (χ : Characters M H) :
    idealCharacter M H hH χ = RayOrthogonality.idealCharacter M (toFullRay M H hH χ) := rfl
end OAI.SevenEighths.RayQuotient
