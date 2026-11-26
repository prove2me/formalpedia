-- Prove2me | solution 1 for NagataFactoriality.dvd_of_localization_dvd_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:32.394935+00:00
-- url     : https://prove2.me/submissions/e510e42e-72f6-468a-b9ab-cfe3d04e5efa

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Theorems.Thm_NagataFactoriality_IsLocalization_dvd_map_iff
import Theorems.Thm_NagataFactoriality_IsLocalization_map_eq_zero_iff
import Theorems.Thm_NagataFactoriality_Localization_den_mul_mk
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_den
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_mk
import Theorems.Thm_NagataFactoriality_Localization_mk_mul_of
import Theorems.Thm_NagataFactoriality_Localization_mk_one
import Theorems.Thm_NagataFactoriality_Localization_of_add
import Theorems.Thm_NagataFactoriality_Localization_of_eq_zero_iff
import Theorems.Thm_NagataFactoriality_Localization_of_mul
import Theorems.Thm_NagataFactoriality_Localization_of_mul_mk
import Theorems.Thm_NagataFactoriality_Localization_of_neg
import Theorems.Thm_NagataFactoriality_Localization_of_one
import Theorems.Thm_NagataFactoriality_Localization_of_zero
import Theorems.Thm_NagataFactoriality_associated_of_irreducible_of_dvd
import Theorems.Thm_NagataFactoriality_associated_symm
import Theorems.Thm_NagataFactoriality_dvd_of_associated
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
import Theorems.Thm_NagataFactoriality_prime_irreducible
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_mem_b89487295096
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c
attribute [local simp] NagataFactoriality.IsLocalization.map_eq_zero_iff
attribute [local simp] NagataFactoriality.Localization.den_mul_mk
attribute [local simp] NagataFactoriality.Localization.mk_mul_den
attribute [local simp] NagataFactoriality.Localization.mk_mul_mk
attribute [local simp] NagataFactoriality.Localization.mk_mul_of
attribute [local simp] NagataFactoriality.Localization.mk_one
attribute [local simp] NagataFactoriality.Localization.of_add
attribute [local simp] NagataFactoriality.Localization.of_eq_zero_iff
attribute [local simp] NagataFactoriality.Localization.of_mul
attribute [local simp] NagataFactoriality.Localization.of_mul_mk
attribute [local simp] NagataFactoriality.Localization.of_neg
attribute [local simp] NagataFactoriality.Localization.of_one
attribute [local simp] NagataFactoriality.Localization.of_zero
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil
attribute [local simp] P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_mem_b89487295096
attribute [local simp] P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
attribute [local simp] P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
attribute [local simp] P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c



set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β] [IsDomain β]
    [_root_.IsLocalization S β] (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p a : α}
    (hp : Irreducible p) (havoid : Avoids S p) (hdiv : algebraMap α β p ∣ algebraMap α β a) :
    p ∣ a := by
  letI : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  rcases (NagataFactoriality.IsLocalization.dvd_map_iff
    (S := S) (β := β) (a := p) (b := a)).1 hdiv with ⟨s, hs, hsa⟩
  rcases hsa with ⟨c, hc⟩
  rcases hS s hs with hsPrime | hsUnit
  · have hsdiv : s ∣ p * c := ⟨a, hc.symm⟩
    rcases hsPrime.2.2 p c hsdiv with hsp | hsc
    · have hsIrred : Irreducible s := prime_irreducible hsPrime
      have hassoc : Associated s p := associated_of_irreducible_of_dvd hsIrred hp hsp
      exact False.elim (havoid s hs (dvd_of_associated (associated_symm hassoc)))
    · rcases hsc with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      have hs0 : s ≠ 0 := hsPrime.ne_zero
      have hcancel : s * a = s * (p * d) := by
        calc
          s * a = p * c := hc
          _ = p * (s * d) := by rw [hd]
          _ = s * (p * d) := by ac_rfl
      exact mul_left_cancel₀ hs0 hcancel
  · rcases hsUnit with ⟨u, rfl⟩
    refine ⟨(↑u⁻¹ : α) * c, ?_⟩
    calc
      a = (↑u⁻¹ : α) * ((u : α) * a) := by simp
      _ = (↑u⁻¹ : α) * (p * c) := by rw [hc]
      _ = p * ((↑u⁻¹ : α) * c) := by ac_rfl
end NagataFactoriality
