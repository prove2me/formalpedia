-- Prove2me | solution 1 for NagataFactoriality.IsLocalization.algebraMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:36.738874+00:00
-- url     : https://prove2.me/submissions/de897d1c-e249-4aba-b7df-fdc885ac533f

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
theorem _root_.solution (S : Submonoid α) [Fact ((0 : α) ∉ S)] [_root_.IsLocalization S β] :
    Function.Injective (algebraMap α β) :=
  let hle : S ≤ nonZeroDivisors α := NagataFactoriality.Submonoid.le_nonZeroDivisors
  _root_.IsLocalization.injective (M := S) (S := β) hle
end NagataFactoriality.IsLocalization
