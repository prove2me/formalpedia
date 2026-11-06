-- Prove2me | solution 1 for OAI.SevenEighths.RayOrthogonality.inUnitSubgroup_globalUnits_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:00:08.443137+00:00
-- url     : https://prove2.me/submissions/b7fc1de3-ad42-433a-af01-426316ea0c3a

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
omit [Finite (A ⧸ M)]
namespace OAI.SevenEighths.RayOrthogonality
theorem _root_.solution (r : A ⧸ M) :
    inUnitSubgroup (globalUnits M) r ↔ principalResidue M r := by
  constructor
  · rintro ⟨u, hur, v, hv⟩
    exact ⟨v, (congrArg Units.val hv).trans hur⟩
  · rintro ⟨u, hu⟩
    exact ⟨Units.map (Ideal.Quotient.mk M).toMonoidHom u, hu, ⟨u, rfl⟩⟩
end OAI.SevenEighths.RayOrthogonality
