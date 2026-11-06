-- Prove2me | solution 1 for OAI.SevenEighths.RayOrthogonality.rayCard_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:01:19.130198+00:00
-- url     : https://prove2.me/submissions/5797b5b5-77c0-4311-b39f-7e6269d549e3

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_ray_card_pos

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
namespace OAI.SevenEighths.RayOrthogonality
theorem _root_.solution : 0 < rayCard M := ray_card_pos _
end OAI.SevenEighths.RayOrthogonality
