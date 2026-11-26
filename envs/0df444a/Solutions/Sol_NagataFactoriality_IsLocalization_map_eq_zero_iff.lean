-- Prove2me | solution 1 for NagataFactoriality.IsLocalization.map_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:36.095885+00:00
-- url     : https://prove2.me/submissions/841b563a-9599-46e2-8e92-48ae1a84dd80

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Theorems.Thm_NagataFactoriality_Submonoid_le_nonZeroDivisors


set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
variable [IsDomain α] [Fact ((0 : α) ∉ S)]
namespace NagataFactoriality.IsLocalization
theorem _root_.solution (S : Submonoid α) [Fact ((0 : α) ∉ S)] [_root_.IsLocalization S β]
    (a : α) : algebraMap α β a = 0 ↔ a = 0 := by
  let hle : S ≤ nonZeroDivisors α := NagataFactoriality.Submonoid.le_nonZeroDivisors
  exact _root_.IsLocalization.to_map_eq_zero_iff (M := S) (S := β) (x := a) hle
end NagataFactoriality.IsLocalization
