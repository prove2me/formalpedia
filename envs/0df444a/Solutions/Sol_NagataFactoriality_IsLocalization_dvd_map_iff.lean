-- Prove2me | solution 1 for NagataFactoriality.IsLocalization.dvd_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:29.823016+00:00
-- url     : https://prove2.me/submissions/5496a225-420e-43dd-83e7-9d7fb719eaa2

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
import Theorems.Thm_NagataFactoriality_IsLocalization_surj
import Theorems.Thm_NagataFactoriality_IsLocalization_algebraMap_injective
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__eq_iff_55bc676ba895
import Theorems.Thm_NagataFactoriality_IsLocalization_map_eq_zero_iff
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil


attribute [local simp] NagataFactoriality.IsLocalization.mk'_mul_map
attribute [local simp] NagataFactoriality.IsLocalization.mk'_one
attribute [local simp] NagataFactoriality.IsLocalization.map_mul_mk'
attribute [local simp] NagataFactoriality.IsLocalization.map_eq_zero_iff

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
variable [IsDomain α] [Fact ((0 : α) ∉ S)]
namespace NagataFactoriality.IsLocalization
theorem _root_.solution {a b : α} :
    algebraMap α β a ∣ algebraMap α β b ↔ ∃ s : α, s ∈ S ∧ a ∣ s * b := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨c, s, hs, rfl⟩ := surj (S := S) (β := β) x
    refine ⟨s, hs, ?_⟩
    have hEq : algebraMap α β b = _root_.IsLocalization.mk' β (a * c) ⟨s, hs⟩ := by
      calc
        algebraMap α β b = algebraMap α β a * _root_.IsLocalization.mk' β c ⟨s, hs⟩ := hx
        _ = _root_.IsLocalization.mk' β (a * c) ⟨s, hs⟩ := map_mul_mk' (S := S) a c s hs
    have hCross : algebraMap α β (b * s) = algebraMap α β (a * c) := by
      have hCross' :
          algebraMap α β b * algebraMap α β s = algebraMap α β (a * c) := by
        exact (_root_.IsLocalization.eq_mk'_iff_mul_eq (M := S) (S := β)
          (z := algebraMap α β b) (x := a * c) (y := ⟨s, hs⟩)).1 hEq
      simpa [map_mul, mul_assoc, mul_left_comm, mul_comm] using hCross'
    refine ⟨c, ?_⟩
    exact by simpa [mul_comm] using (algebraMap_injective (α := α) (β := β) S hCross)
  · rintro ⟨s, hs, c, hc⟩
    refine ⟨_root_.IsLocalization.mk' β c ⟨s, hs⟩, ?_⟩
    symm
    calc
      algebraMap α β a * _root_.IsLocalization.mk' β c ⟨s, hs⟩ =
          _root_.IsLocalization.mk' β (a * c) ⟨s, hs⟩ := map_mul_mk' (S := S) a c s hs
      _ = _root_.IsLocalization.mk' β b ⟨1, S.one_mem⟩ := by
        apply (mk'_eq_iff (S := S) (β := β) (hs := hs) (ht := S.one_mem)).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hc.symm
      _ = algebraMap α β b := mk'_one (S := S) (β := β) b
end NagataFactoriality.IsLocalization
