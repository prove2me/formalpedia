-- Prove2me | solution 1 for NagataFactoriality.Localization.isUnit_mk_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:26.150173+00:00
-- url     : https://prove2.me/submissions/2c73c107-3b58-40cf-92c1-b0bfe71e5b71

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
import Theorems.Thm_NagataFactoriality_Localization_isUnit_mk_of_mem
import Theorems.Thm_NagataFactoriality_Localization_isUnit_of_isUnit
import Theorems.Thm_NagataFactoriality_isUnit_mul
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
theorem _root_.solution {a s : α} (ha : IsUnit a) (hs : s ∈ S) :
    IsUnit (mk (S := S) a s hs) := by
  have hmk : mk (S := S) a s hs = of (S := S) a * mk (S := S) 1 s hs := by
    calc
      mk (S := S) a s hs = mk (S := S) (a * 1) s hs := by simp
      _ = of (S := S) a * mk (S := S) 1 s hs := by
        rw [← of_mul_mk (S := S) a 1 s hs]
  rw [hmk]
  exact isUnit_mul (isUnit_of_isUnit (S := S) ha) (isUnit_mk_of_mem (S := S) S.one_mem hs)
end NagataFactoriality.Localization
