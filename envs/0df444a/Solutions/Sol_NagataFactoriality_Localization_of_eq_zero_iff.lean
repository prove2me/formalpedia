-- Prove2me | solution 1 for NagataFactoriality.Localization.of_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:43.374798+00:00
-- url     : https://prove2.me/submissions/a0226da5-e7d7-464b-a36e-0f2b1d160432

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
import Theorems.Thm_NagataFactoriality_Submonoid_le_nonZeroDivisors


set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
variable [IsDomain α] [Fact ((0 : α) ∉ S)]
namespace NagataFactoriality.Localization
theorem _root_.solution (a : α) : of (S := S) a = 0 ↔ a = 0 := by
  show algebraMap α (Localization S) a = 0 ↔ a = 0
  exact IsLocalization.to_map_eq_zero_iff (M := S) (S := Localization S) (x := a)
    (Submonoid.le_nonZeroDivisors (S := S))
end NagataFactoriality.Localization
