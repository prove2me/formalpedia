-- Prove2me | solution 1 for NagataFactoriality.Localization.mk_mul_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:56:56.395517+00:00
-- url     : https://prove2.me/submissions/43b2502a-be16-4c14-977f-99cd40903ef7

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
import Theorems.Thm_NagataFactoriality_Localization_of_mul_mk
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil


attribute [local simp] NagataFactoriality.Localization.of_mul_mk

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
namespace NagataFactoriality.Localization
theorem _root_.solution (a b s : α) (hs : s ∈ S) :
    mk (S := S) a s hs * of (S := S) b = mk (S := S) (a * b) s hs := by
  calc
    mk (S := S) a s hs * of (S := S) b =
        of (S := S) b * mk (S := S) a s hs := by rw [mul_comm]
    _ = mk (S := S) (b * a) s hs := of_mul_mk (S := S) b a s hs
    _ = mk (S := S) (a * b) s hs := by rw [mul_comm]
end NagataFactoriality.Localization
