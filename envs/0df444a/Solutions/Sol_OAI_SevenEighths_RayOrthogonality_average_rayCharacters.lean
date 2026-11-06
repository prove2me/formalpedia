-- Prove2me | solution 1 for OAI.SevenEighths.RayOrthogonality.average_rayCharacters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:04:07.212771+00:00
-- url     : https://prove2.me/submissions/2012f47c-8a67-45fd-91fb-898387f13b7d

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_average_characters
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_inUnitSubgroup_globalUnits_iff

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
namespace OAI.SevenEighths.RayOrthogonality
theorem _root_.solution (r : A ⧸ M) :
    (∑ χ : rayCharacters M, (χ : MulChar (A ⧸ M) ℂ) r) / (rayCard M : ℂ) =
      if principalResidue M r then 1 else 0 := by
  rw [average_characters, inUnitSubgroup_globalUnits_iff]
end OAI.SevenEighths.RayOrthogonality
