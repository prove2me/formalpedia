-- Prove2me | solution 1 for NagataFactoriality.Localization.mk_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:11.427108+00:00
-- url     : https://prove2.me/submissions/fe24f7a9-9ea9-4064-bdd7-cf204132666a

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil



set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
namespace NagataFactoriality.Localization
theorem _root_.solution (a : α) : mk (S := S) a 1 S.one_mem = of (S := S) a := by
  have hden : (⟨1, S.one_mem⟩ : S) = 1 := Subtype.ext (by rfl)
  simpa only [mk, of, hden] using (_root_.Localization.mk_one_eq_algebraMap (M := S) a)
end NagataFactoriality.Localization
