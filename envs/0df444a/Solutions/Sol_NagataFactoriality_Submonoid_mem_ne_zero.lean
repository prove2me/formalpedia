-- Prove2me | solution 1 for NagataFactoriality.Submonoid.mem_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:49:20.040501+00:00
-- url     : https://prove2.me/submissions/c18b3341-62a9-46c4-b5a0-e18d9e43ff61

import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil



set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Submonoid
variable {α : Type*} [CommRing α] [IsDomain α]
omit [IsDomain α]
namespace NagataFactoriality.Submonoid
theorem _root_.solution {S : Submonoid α} [Fact ((0 : α) ∉ S)] {s : α} (hs : s ∈ S) : s ≠ 0 := by
  intro hs0
  have h0 : (0 : α) ∈ S := by simpa [hs0] using hs
  exact (Fact.out : (0 : α) ∉ S) h0
end NagataFactoriality.Submonoid
