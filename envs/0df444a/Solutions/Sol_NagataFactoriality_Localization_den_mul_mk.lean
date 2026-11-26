-- Prove2me | solution 1 for NagataFactoriality.Localization.den_mul_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:23.431482+00:00
-- url     : https://prove2.me/submissions/26fefebe-b9e6-4d41-81ee-b49ce694543a

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_den
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil


attribute [local simp] NagataFactoriality.Localization.mk_mul_den

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
namespace NagataFactoriality.Localization
theorem _root_.solution (a s : α) (hs : s ∈ S) :
    of (S := S) s * mk (S := S) a s hs = of (S := S) a := by
  rw [mul_comm]
  exact mk_mul_den (S := S) a s hs
end NagataFactoriality.Localization
