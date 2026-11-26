-- Prove2me | solution 1 for NagataFactoriality.Localization.mk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:37.343257+00:00
-- url     : https://prove2.me/submissions/ff23012f-e6b3-4509-b9f7-6dd48dbcf8f0

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
import Theorems.Thm_NagataFactoriality_Localization_algebraMap_injective
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

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
variable [IsDomain α] [Fact ((0 : α) ∉ S)]
namespace NagataFactoriality.Localization
theorem _root_.solution {a b s t : α} (hs : s ∈ S) (ht : t ∈ S) :
    mk (S := S) a s hs = mk (S := S) b t ht ↔ a * t = b * s := by
  constructor
  · intro h
    have h' :
        algebraMap α (Localization S) (a * t) = algebraMap α (Localization S) (b * s) := by
      have h'' :
          IsLocalization.mk' (Localization S) a ⟨s, hs⟩ =
            IsLocalization.mk' (Localization S) b ⟨t, ht⟩ := by
        simpa [mk, _root_.Localization.mk_eq_mk'_apply] using h
      exact (IsLocalization.mk'_eq_iff_eq' (M := S) (S := Localization S)).1 h''
    exact algebraMap_injective (S := S) <|
      by simpa [map_mul, mul_assoc, mul_left_comm, mul_comm] using h'
  · intro h
    have h' :
        IsLocalization.mk' (Localization S) a ⟨s, hs⟩ =
          IsLocalization.mk' (Localization S) b ⟨t, ht⟩ := by
      exact IsLocalization.mk'_eq_of_eq' (M := S) (S := Localization S) <|
        by simpa [mul_assoc, mul_left_comm, mul_comm] using h.symm
    simpa [mk, _root_.Localization.mk_eq_mk'_apply] using h'
end NagataFactoriality.Localization
