-- Prove2me | solution 1 for OAI.SevenEighths.RayQuotient.classNumber_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:01:19.655612+00:00
-- url     : https://prove2.me/submissions/0935517c-9e9b-4ced-b860-ade80f739fcf

import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayQuotient
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_ray_card_pos


set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)
namespace OAI.SevenEighths.RayQuotient
theorem _root_.solution : 0 < classNumber M H := ray_card_pos H
end OAI.SevenEighths.RayQuotient
