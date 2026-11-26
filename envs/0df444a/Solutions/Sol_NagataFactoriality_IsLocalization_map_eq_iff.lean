-- Prove2me | solution 1 for NagataFactoriality.IsLocalization.map_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:56.078441+00:00
-- url     : https://prove2.me/submissions/7f673d3b-d9f1-4cb6-b298-b5c9f5608aca

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Theorems.Thm_NagataFactoriality_IsLocalization_algebraMap_injective

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
variable [IsDomain α] [Fact ((0 : α) ∉ S)]
namespace NagataFactoriality.IsLocalization
theorem _root_.solution (S : Submonoid α) [Fact ((0 : α) ∉ S)] [_root_.IsLocalization S β] (a b : α) :
    algebraMap α β a = algebraMap α β b ↔ a = b :=
  (algebraMap_injective (α := α) (β := β) S).eq_iff
end NagataFactoriality.IsLocalization
