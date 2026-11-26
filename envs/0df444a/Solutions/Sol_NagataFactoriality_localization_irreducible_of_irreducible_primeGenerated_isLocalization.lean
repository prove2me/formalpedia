-- Prove2me | solution 1 for NagataFactoriality.localization_irreducible_of_irreducible_primeGenerated_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:01:07.709739+00:00
-- url     : https://prove2.me/submissions/450b3941-6a97-4857-ad11-9119e3ca08e9

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Theorems.Thm_NagataFactoriality_multiset_prod_mem_of_factors
import Theorems.Thm_NagataFactoriality_split_prime_factors_of_mul_eq
import Theorems.Thm_NagataFactoriality_IsLocalization_dvd_map_iff
import Theorems.Thm_NagataFactoriality_IsLocalization_isUnit_map_of_mem
import Theorems.Thm_NagataFactoriality_IsLocalization_map_eq_zero_iff
import Theorems.Thm_NagataFactoriality_IsLocalization_surj
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
import Theorems.Thm_NagataFactoriality_Localization_surj
import Theorems.Thm_NagataFactoriality_isUnit_mul
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_isUnit_e79c2341041d
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_mem_b89487295096
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__eq_iff_55bc676ba895
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
    [_root_.IsLocalization S β] (hS : PrimeGenerated S) {p : α} (hp : Irreducible p)
    (havoid : Avoids S p) : Irreducible (algebraMap α β p) := by
  letI : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  refine ⟨?_, ?_⟩
  · intro hunit
    have hdiv : algebraMap α β p ∣ (1 : β) := by
      rcases isUnit_iff_exists_inv.mp hunit with ⟨x, hx⟩
      exact ⟨x, hx.symm⟩
    have hdiv' : algebraMap α β p ∣ algebraMap α β (1 : α) := by
      simpa using hdiv
    rcases (NagataFactoriality.IsLocalization.dvd_map_iff
      (S := S) (β := β) (a := p) (b := 1)).1 hdiv' with ⟨s, hs, hps⟩
    exact havoid s hs (by simpa using hps)
  · intro x y hxy
    obtain ⟨a, s, hs, rfl⟩ := NagataFactoriality.IsLocalization.surj (S := S) (β := β) x
    obtain ⟨b, t, ht, rfl⟩ := NagataFactoriality.IsLocalization.surj (S := S) (β := β) y
    have hEq :
        p * (s * t) = a * b := by
      have hloc :
          algebraMap α β p =
            _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := by
        calc
          algebraMap α β p =
              _root_.IsLocalization.mk' β a ⟨s, hs⟩ * _root_.IsLocalization.mk' β b ⟨t, ht⟩ := hxy
          _ = _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := by
              simpa using (_root_.IsLocalization.mk'_mul
                (M := S) (S := β) a b ⟨s, hs⟩ ⟨t, ht⟩).symm
      have hmk :
          _root_.IsLocalization.mk' β p ⟨1, S.one_mem⟩ =
            _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := by
        calc
          _root_.IsLocalization.mk' β p ⟨1, S.one_mem⟩ = algebraMap α β p := by
            exact NagataFactoriality.IsLocalization.mk'_one (S := S) (β := β) p
          _ = _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := hloc
      simpa [mul_one] using
        (NagataFactoriality.IsLocalization.mk'_eq_iff
          (S := S) (β := β) (a := p) (b := a * b)
          (s := 1) (t := s * t) S.one_mem (S.mul_mem hs ht)).1 hmk
    rcases hS (s * t) (S.mul_mem hs ht) with ⟨f, hf, hfprod⟩
    rcases split_prime_factors_of_mul_eq (fun q hq => (hf q hq).2) hp (by simpa [hfprod] using hEq)
        with ⟨f₁, f₂, a', b', hpart, ha, hb, hpab⟩
    rcases hp.isUnit_or_isUnit hpab with haUnit | hbUnit
    · left
      have hf₁mem : ∀ q ∈ f₁, q ∈ S := by
        intro q hq
        exact (hf q (by rw [← hpart]; exact Multiset.mem_add.mpr (Or.inl hq))).1
      have hprodMem : f₁.prod ∈ S := multiset_prod_mem_of_factors hf₁mem
      have hx_eq :
          _root_.IsLocalization.mk' β a ⟨s, hs⟩ =
            algebraMap α β f₁.prod * _root_.IsLocalization.mk' β a' ⟨s, hs⟩ := by
        rw [ha]
        symm
        exact NagataFactoriality.IsLocalization.map_mul_mk' (S := S) (β := β) f₁.prod a' s hs
      rw [hx_eq]
      exact isUnit_mul
        (NagataFactoriality.IsLocalization.isUnit_map_of_mem (S := S) (β := β) hprodMem)
        (NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit (S := S) (β := β) haUnit hs)
    · right
      have hf₂mem : ∀ q ∈ f₂, q ∈ S := by
        intro q hq
        exact (hf q (by rw [← hpart]; exact Multiset.mem_add.mpr (Or.inr hq))).1
      have hprodMem : f₂.prod ∈ S := multiset_prod_mem_of_factors hf₂mem
      have hy_eq :
          _root_.IsLocalization.mk' β b ⟨t, ht⟩ =
            algebraMap α β f₂.prod * _root_.IsLocalization.mk' β b' ⟨t, ht⟩ := by
        rw [hb]
        symm
        exact NagataFactoriality.IsLocalization.map_mul_mk' (S := S) (β := β) f₂.prod b' t ht
      rw [hy_eq]
      exact isUnit_mul
        (NagataFactoriality.IsLocalization.isUnit_map_of_mem (S := S) (β := β) hprodMem)
        (NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit (S := S) (β := β) hbUnit ht)
end NagataFactoriality
