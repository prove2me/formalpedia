-- Prove2me | solution 1 for OAI.SevenEighths.RayOrthogonality.sum_rayCharacters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:03:20.617818+00:00
-- url     : https://prove2.me/submissions/5210f445-9e87-4982-b58b-b6301279fb69

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_sum_characters
import Theorems.Thm_OAI_SevenEighths_RayOrthogonality_inUnitSubgroup_globalUnits_iff

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
namespace OAI.SevenEighths.RayOrthogonality
theorem _root_.solution (r : A ⧸ M) :
    ∑ χ : rayCharacters M, (χ : MulChar (A ⧸ M) ℂ) r =
      if principalResidue M r then (rayCard M : ℂ) else 0 := by
  rw [sum_characters, inUnitSubgroup_globalUnits_iff]
end OAI.SevenEighths.RayOrthogonality
