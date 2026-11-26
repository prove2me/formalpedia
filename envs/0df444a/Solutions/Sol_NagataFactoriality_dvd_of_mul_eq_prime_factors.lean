-- Prove2me | solution 1 for NagataFactoriality.dvd_of_mul_eq_prime_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:12.083648+00:00
-- url     : https://prove2.me/submissions/87237c5b-cefc-42e6-855e-54f0c70072ed

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
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
theorem _root_.solution {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) {p a c : α} (hp : Irreducible p)
    (hnot : ∀ q ∈ f, ¬ p ∣ q) (hEq : f.prod * a = p * c) : p ∣ a := by
  have hmain :
      ∀ g : Multiset α, (∀ q ∈ g, Prime q) → (∀ q ∈ g, ¬ p ∣ q) →
        ∀ {d : α}, g.prod * a = p * d → p ∣ a := by
    intro g
    refine Multiset.induction_on g ?_ ?_
    · intro hg hnotg d hEqg
      refine ⟨d, ?_⟩
      simpa using hEqg
    · intro q qs ih hqs hnotqs d hEqqs
      have hq : Prime q := hqs q (by simp)
      have htail : ∀ r ∈ qs, Prime r := by
        intro r hr
        exact hqs r (by simp [hr])
      have htailNot : ∀ r ∈ qs, ¬ p ∣ r := by
        intro r hr
        exact hnotqs r (by simp [hr])
      have hqNot : ¬ p ∣ q := hnotqs q (by simp)
      have hq_dvd : q ∣ p * d := by
        refine ⟨qs.prod * a, ?_⟩
        simpa [mul_assoc] using hEqqs.symm
      rcases hq.2.2 p d hq_dvd with hqp | hqc
      · have hqIrred : Irreducible q := prime_irreducible hq
        have hassoc : Associated q p := associated_of_irreducible_of_dvd hqIrred hp hqp
        exact False.elim (hqNot (dvd_of_associated (associated_symm hassoc)))
      · rcases hqc with ⟨e, hd⟩
        have hq0 : q ≠ 0 := hq.ne_zero
        have hEq' : q * (qs.prod * a) = q * (p * e) := by
          calc
            q * (qs.prod * a) = (q ::ₘ qs).prod * a := by simp [mul_assoc]
            _ = p * d := hEqqs
            _ = p * (q * e) := by rw [hd]
            _ = q * (p * e) := by ac_rfl
        have hcancel : qs.prod * a = p * e := mul_left_cancel₀ hq0 hEq'
        exact ih htail htailNot hcancel
  exact hmain f hf hnot hEq
end NagataFactoriality
