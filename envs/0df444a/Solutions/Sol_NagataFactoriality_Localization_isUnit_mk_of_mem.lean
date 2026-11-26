-- Prove2me | solution 1 for NagataFactoriality.Localization.isUnit_mk_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:30.999827+00:00
-- url     : https://prove2.me/submissions/a4400b8e-d155-4b38-aa0a-6a5ff36a6fe3

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
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_mk
import Theorems.Thm_NagataFactoriality_Localization_of_mul_mk
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_of
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
attribute [local simp] NagataFactoriality.Localization.mk_mul_mk
attribute [local simp] NagataFactoriality.Localization.of_mul_mk
attribute [local simp] NagataFactoriality.Localization.mk_mul_of

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
namespace NagataFactoriality.Localization
theorem _root_.solution {a s : α} (ha : a ∈ S) (hs : s ∈ S) :
    IsUnit (mk (S := S) a s hs) := by
  apply isUnit_iff_exists_inv.2
  refine ⟨mk (S := S) s a ha, ?_⟩
  simpa [mk, _root_.Localization.mk_eq_mk'_apply] using
    (IsLocalization.mk'_mul_mk'_eq_one' (M := S) (S := Localization S) a ⟨s, hs⟩ ha)
end NagataFactoriality.Localization
