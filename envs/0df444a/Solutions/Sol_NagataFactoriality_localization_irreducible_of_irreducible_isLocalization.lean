-- Prove2me | solution 1 for NagataFactoriality.localization_irreducible_of_irreducible_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:31.76601+00:00
-- url     : https://prove2.me/submissions/07c54a05-ade8-4154-8a7e-f424251459b6

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Theorems.Thm_NagataFactoriality_IsLocalization_dvd_map_iff
import Theorems.Thm_NagataFactoriality_IsLocalization_isUnit_map_of_isUnit
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
    [_root_.IsLocalization S β] (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p : α}
    (hp : Irreducible p) (havoid : Avoids S p) : Irreducible (algebraMap α β p) := by
  letI : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
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
    have hprod : p * (s * t) = a * b := by
      have hEq :
          algebraMap α β p =
            _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := by
        calc
          algebraMap α β p =
              _root_.IsLocalization.mk' β a ⟨s, hs⟩ * _root_.IsLocalization.mk' β b ⟨t, ht⟩ := hxy
          _ = _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := by
              simpa using (_root_.IsLocalization.mk'_mul
                (M := S) (S := β) a b ⟨s, hs⟩ ⟨t, ht⟩).symm
      have hEq' :
          _root_.IsLocalization.mk' β p ⟨1, S.one_mem⟩ =
            _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := by
        calc
          _root_.IsLocalization.mk' β p ⟨1, S.one_mem⟩ = algebraMap α β p := by
            exact NagataFactoriality.IsLocalization.mk'_one (S := S) (β := β) p
          _ = _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := hEq
      simpa [mul_one] using
        (NagataFactoriality.IsLocalization.mk'_eq_iff
          (S := S) (β := β) (a := p) (b := a * b)
          (s := 1) (t := s * t) S.one_mem (S.mul_mem hs ht)).1 hEq'
    rcases hS (s * t) (S.mul_mem hs ht) with hstPrime | hstUnit
    · have hstdiv : s * t ∣ a * b := by
        refine ⟨p, ?_⟩
        calc
          a * b = p * (s * t) := hprod.symm
          _ = (s * t) * p := by ac_rfl
      rcases hstPrime.2.2 a b hstdiv with hdiva | hdivb
      · rcases hdiva with ⟨d, hd⟩
        have hst0 : s * t ≠ 0 := hstPrime.ne_zero
        have hp_eq : p = d * b := by
          apply mul_left_cancel₀ hst0
          calc
            (s * t) * p = p * (s * t) := by ac_rfl
            _ = a * b := hprod
            _ = ((s * t) * d) * b := by rw [hd]
            _ = (s * t) * (d * b) := by ac_rfl
        rcases hp.isUnit_or_isUnit hp_eq with hdUnit | hbUnit
        · left
          have hx_eq_mk :
              _root_.IsLocalization.mk' β a ⟨s, hs⟩ =
                _root_.IsLocalization.mk' β (t * d) ⟨1, S.one_mem⟩ := by
            apply (NagataFactoriality.IsLocalization.mk'_eq_iff
              (S := S) (β := β) (a := a) (b := t * d)
              (s := s) (t := 1) hs S.one_mem).2
            calc
              a * 1 = a := by simp
              _ = s * t * d := by rw [hd]
              _ = (t * d) * s := by ac_rfl
          have hx_eq : _root_.IsLocalization.mk' β a ⟨s, hs⟩ = algebraMap α β (t * d) := by
            calc
              _root_.IsLocalization.mk' β a ⟨s, hs⟩ =
                  _root_.IsLocalization.mk' β (t * d) ⟨1, S.one_mem⟩ := hx_eq_mk
              _ = algebraMap α β (t * d) := by
                  exact NagataFactoriality.IsLocalization.mk'_one (S := S) (β := β) (t * d)
          rw [hx_eq]
          have htUnitLoc : IsUnit (algebraMap α β t) :=
            NagataFactoriality.IsLocalization.isUnit_map_of_mem (S := S) (β := β) ht
          have hdUnitLoc : IsUnit (algebraMap α β d) :=
            NagataFactoriality.IsLocalization.isUnit_map_of_isUnit (β := β) hdUnit
          simpa [map_mul] using isUnit_mul htUnitLoc hdUnitLoc
        · right
          exact NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit
            (S := S) (β := β) hbUnit ht
      · rcases hdivb with ⟨d, hd⟩
        have hst0 : s * t ≠ 0 := hstPrime.ne_zero
        have hp_eq : p = a * d := by
          apply mul_left_cancel₀ hst0
          calc
            (s * t) * p = p * (s * t) := by ac_rfl
            _ = a * b := hprod
            _ = a * ((s * t) * d) := by rw [hd]
            _ = (s * t) * (a * d) := by ac_rfl
        rcases hp.isUnit_or_isUnit hp_eq with haUnit | hdUnit
        · left
          exact NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit
            (S := S) (β := β) haUnit hs
        · right
          have hy_eq_mk :
              _root_.IsLocalization.mk' β b ⟨t, ht⟩ =
                _root_.IsLocalization.mk' β (s * d) ⟨1, S.one_mem⟩ := by
            apply (NagataFactoriality.IsLocalization.mk'_eq_iff
              (S := S) (β := β) (a := b) (b := s * d)
              (s := t) (t := 1) ht S.one_mem).2
            calc
              b * 1 = b := by simp
              _ = s * t * d := by rw [hd]
              _ = (s * d) * t := by ac_rfl
          have hy_eq : _root_.IsLocalization.mk' β b ⟨t, ht⟩ = algebraMap α β (s * d) := by
            calc
              _root_.IsLocalization.mk' β b ⟨t, ht⟩ =
                  _root_.IsLocalization.mk' β (s * d) ⟨1, S.one_mem⟩ := hy_eq_mk
              _ = algebraMap α β (s * d) := by
                  exact NagataFactoriality.IsLocalization.mk'_one (S := S) (β := β) (s * d)
          rw [hy_eq]
          have hsUnitLoc : IsUnit (algebraMap α β s) :=
            NagataFactoriality.IsLocalization.isUnit_map_of_mem (S := S) (β := β) hs
          have hdUnitLoc : IsUnit (algebraMap α β d) :=
            NagataFactoriality.IsLocalization.isUnit_map_of_isUnit (β := β) hdUnit
          simpa [map_mul] using isUnit_mul hsUnitLoc hdUnitLoc
    · have hassoc : Associated p (a * b) := by
        simpa [hprod] using associated_mul_unit_right p (s * t) hstUnit
      have habIrred : Irreducible (a * b) := hassoc.irreducible hp
      exact (habIrred.isUnit_or_isUnit rfl).elim
        (fun haUnit => Or.inl <|
          NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit (S := S) (β := β) haUnit hs)
        (fun hbUnit => Or.inr <|
          NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit (S := S) (β := β) hbUnit ht)
end NagataFactoriality
