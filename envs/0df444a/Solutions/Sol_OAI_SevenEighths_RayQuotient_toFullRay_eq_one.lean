-- Prove2me | solution 1 for OAI.SevenEighths.RayQuotient.toFullRay_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:02:00.376673+00:00
-- url     : https://prove2.me/submissions/01ac08ee-2515-4a9c-8242-02c24681c49c

import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayQuotient
import Theorems.Thm_OAI_SevenEighths_RayQuotient_toFullRay_injective

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)
include hH
namespace OAI.SevenEighths.RayQuotient
theorem _root_.solution (χ : Characters M H) :
    toFullRay M H hH χ = 1 ↔ χ = 1 := by
  rw [← map_one (toFullRay M H hH)]
  exact (toFullRay_injective M H hH).eq_iff
end OAI.SevenEighths.RayQuotient
