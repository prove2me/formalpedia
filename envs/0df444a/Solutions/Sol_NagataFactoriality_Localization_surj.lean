-- Prove2me | solution 1 for NagataFactoriality.Localization.surj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:36.843641+00:00
-- url     : https://prove2.me/submissions/b1463587-9cfe-4ccf-b301-a87e0981653a

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
namespace NagataFactoriality.Localization
theorem _root_.solution (z : Localization S) : ∃ a s, ∃ hs : s ∈ S, z = mk (S := S) a s hs := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (M := S) (S := Localization S) z
  exact ⟨a, s, s.property, by
    simpa [mk, _root_.Localization.mk_eq_mk'_apply] using hs.symm⟩
end NagataFactoriality.Localization
