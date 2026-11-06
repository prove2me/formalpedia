-- Prove2me | solution 1 for OAI.SevenEighths.RayOrthogonality.card_characters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:00:18.174236+00:00
-- url     : https://prove2.me/submissions/cfdc6903-572b-4d24-92ef-066aeffe3b92

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {R : Type*} [CommMonoid R] [Finite R]
namespace OAI.SevenEighths.RayOrthogonality
theorem _root_.solution (H : Subgroup Rˣ) :
    Fintype.card (characters H) = Nat.card (Rˣ ⧸ H) := by
  rw [← Nat.card_eq_fintype_card]
  exact MulChar.card_subgroupOrderIsoSubgroupMulChar
end OAI.SevenEighths.RayOrthogonality
