-- Prove2me | solution 1 for NagataFactoriality.Localization.dvd_of_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:31.993575+00:00
-- url     : https://prove2.me/submissions/aa06b211-53d8-4ce9-8bfa-66555b38166d

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
import Theorems.Thm_NagataFactoriality_Localization_surj
import Theorems.Thm_NagataFactoriality_Localization_algebraMap_injective
import Theorems.Thm_NagataFactoriality_Localization_mk_eq_iff
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
variable [IsDomain α] [Fact ((0 : α) ∉ S)]
namespace NagataFactoriality.Localization
theorem _root_.solution {a b : α} :
    of (S := S) a ∣ of (S := S) b ↔ ∃ s : α, s ∈ S ∧ a ∣ s * b := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨c, s, hs, rfl⟩ := surj (S := S) x
    refine ⟨s, hs, ?_⟩
    have hEq : of (S := S) b = mk (S := S) (a * c) s hs := by
      calc
        of (S := S) b = of (S := S) a * mk (S := S) c s hs := hx
        _ = mk (S := S) (a * c) s hs := of_mul_mk (S := S) a c s hs
    have hCross :
        algebraMap α (Localization S) (b * s) = algebraMap α (Localization S) (a * c) := by
      have hCross' :
          of (S := S) b * algebraMap α (Localization S) s =
            algebraMap α (Localization S) (a * c) := by
        exact (IsLocalization.eq_mk'_iff_mul_eq (M := S) (S := Localization S)
          (z := of (S := S) b) (x := a * c) (y := ⟨s, hs⟩)).1 <|
            by simpa [mk, of, _root_.Localization.mk_eq_mk'_apply] using hEq
      simpa [of, map_mul, mul_assoc, mul_left_comm, mul_comm] using hCross'
    have hEq' : b * s = a * c := (algebraMap_injective (S := S)) hCross
    exact ⟨c, by simpa [mul_comm] using hEq'⟩
  · rintro ⟨s, hs, c, hc⟩
    refine ⟨mk (S := S) c s hs, ?_⟩
    symm
    calc
      of (S := S) a * mk (S := S) c s hs = mk (S := S) (a * c) s hs :=
        of_mul_mk (S := S) a c s hs
      _ = of (S := S) b := by
        apply (mk_eq_iff (S := S) (hs := hs) (ht := S.one_mem)).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hc.symm
end NagataFactoriality.Localization
