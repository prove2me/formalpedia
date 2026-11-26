-- Prove2me | solution 1 for NagataFactoriality.Localization.algebraMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:16.165592+00:00
-- url     : https://prove2.me/submissions/4c69fc1c-e4d6-43a0-992e-5b79df7facee

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
theorem _root_.solution : Function.Injective (algebraMap α (Localization S)) :=
  IsLocalization.injective (M := S) (S := Localization S) (Submonoid.le_nonZeroDivisors (S := S))
end NagataFactoriality.Localization
