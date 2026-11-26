-- Prove2me | solution 1 for NagataFactoriality.prime_of_irreducible_of_dvd_prime_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:08.42261+00:00
-- url     : https://prove2.me/submissions/6fbb98a8-e876-4863-b0e9-fa1c6c24804d

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
import Theorems.Thm_NagataFactoriality_isUnit_of_dvd_one
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
import Theorems.Thm_NagataFactoriality_prime_irreducible
import Theorems.Thm_NagataFactoriality_prime_of_associated
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
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) {p : α}
    (hp : Irreducible p) (hdiv : p ∣ f.prod) : Prime p := by
  revert hf hdiv
  refine Multiset.induction_on f ?_ ?_
  · intro _ hdiv
    exact False.elim (hp.not_isUnit (isUnit_of_dvd_one (by simpa using hdiv)))
  · intro q qs ih hqs hdiv
    have hq : Prime q := hqs q (by simp)
    have htail : ∀ r ∈ qs, Prime r := by
      intro r hr
      exact hqs r (by simp [hr])
    rcases hdiv with ⟨d, hd⟩
    have hq_dvd : q ∣ p * d := by
      refine ⟨qs.prod, ?_⟩
      simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hd.symm
    rcases hq.2.2 p d hq_dvd with hqp | hqd
    · have hqIrred : Irreducible q := prime_irreducible hq
      have hassoc : Associated q p := associated_of_irreducible_of_dvd hqIrred hp hqp
      exact prime_of_associated hq hassoc
    · rcases hqd with ⟨e, hde⟩
      have hcancel : qs.prod = p * e := by
        apply mul_left_cancel₀ hq.ne_zero
        calc
          q * qs.prod = p * d := by simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hd
          _ = p * (q * e) := by rw [hde]
          _ = q * (p * e) := by ac_rfl
      exact ih htail ⟨e, hcancel⟩
end NagataFactoriality
