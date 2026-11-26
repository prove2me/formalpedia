-- Prove2me | solution 1 for NagataFactoriality.Localization.mk_mul_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:36.402799+00:00
-- url     : https://prove2.me/submissions/b0554de2-8a0b-43c8-badb-5d2168fe0f53

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization
import Theorems.Thm_NagataFactoriality_Localization_mk_one
import Theorems.Thm_NagataFactoriality_Localization_of_zero
import Theorems.Thm_NagataFactoriality_Localization_of_one
import Theorems.Thm_NagataFactoriality_Localization_of_add
import Theorems.Thm_NagataFactoriality_Localization_of_mul
import Theorems.Thm_NagataFactoriality_Localization_of_neg
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_den
import Theorems.Thm_NagataFactoriality_Localization_den_mul_mk
import Theorems.Thm_NagataFactoriality_Localization_of_eq_zero_iff
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil


attribute [local simp] NagataFactoriality.Localization.mk_one
attribute [local simp] NagataFactoriality.Localization.of_zero
attribute [local simp] NagataFactoriality.Localization.of_one
attribute [local simp] NagataFactoriality.Localization.of_add
attribute [local simp] NagataFactoriality.Localization.of_mul
attribute [local simp] NagataFactoriality.Localization.of_neg
attribute [local simp] NagataFactoriality.Localization.mk_mul_den
attribute [local simp] NagataFactoriality.Localization.den_mul_mk
attribute [local simp] NagataFactoriality.Localization.of_eq_zero_iff

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
namespace NagataFactoriality.Localization
theorem _root_.solution {a b s t : α} (hs : s ∈ S) (ht : t ∈ S) :
    mk (S := S) a s hs * mk (S := S) b t ht =
      mk (S := S) (a * b) (s * t) (S.mul_mem hs ht) := by
  simpa [mk, _root_.Localization.mk_eq_mk'_apply] using
    (IsLocalization.mk'_mul (M := S) (S := Localization S) a b ⟨s, hs⟩ ⟨t, ht⟩).symm
end NagataFactoriality.Localization
