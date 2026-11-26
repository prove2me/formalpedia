-- Prove2me | solution 1 for NagataFactoriality.Localization.of_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:53:01.195962+00:00
-- url     : https://prove2.me/submissions/1e9d88e6-e6b7-450b-ad68-fddb5b777003

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
import Theorems.Thm_NagataFactoriality_Localization_algebraMap_injective

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
variable [IsDomain α] [Fact ((0 : α) ∉ S)]
namespace NagataFactoriality.Localization
theorem _root_.solution (a b : α) : of (S := S) a = of (S := S) b ↔ a = b :=
  (algebraMap_injective (S := S)).eq_iff
end NagataFactoriality.Localization
