-- Prove2me | solution 1 for NagataFactoriality.split_prime_factors_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:19.033805+00:00
-- url     : https://prove2.me/submissions/502031b8-6c26-4840-b971-a40500e8b47b

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
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
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
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) {p a b : α} (_hp : Irreducible p)
    (hEq : p * f.prod = a * b) :
    ∃ f₁ f₂ : Multiset α, ∃ a' b' : α,
      f₁ + f₂ = f ∧
      a = f₁.prod * a' ∧
      b = f₂.prod * b' ∧
      p = a' * b' := by
  have hmain :
      ∀ (g : Multiset α) (a b : α), (∀ q ∈ g, Prime q) → p * g.prod = a * b →
        ∃ f₁ f₂ : Multiset α, ∃ a' b' : α,
          f₁ + f₂ = g ∧
          a = f₁.prod * a' ∧
          b = f₂.prod * b' ∧
          p = a' * b' := by
    intro g
    refine Multiset.induction_on g ?_ ?_
    · intro a b _ hEq
      refine ⟨0, 0, a, b, rfl, ?_, ?_, ?_⟩
      · simp
      · simp
      · simpa using hEq
    · intro q qs ih a b hqs hEq
      have hq : Prime q := hqs q (by simp)
      have htail : ∀ r ∈ qs, Prime r := by
        intro r hr
        exact hqs r (by simp [hr])
      have hq_dvd_ab : q ∣ a * b := by
        refine ⟨p * qs.prod, ?_⟩
        calc
          a * b = p * (q * qs.prod) := by
            simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hEq.symm
          _ = q * (p * qs.prod) := by ac_rfl
      rcases hq.2.2 a b hq_dvd_ab with hqa | hqb
      · rcases hqa with ⟨a₁, ha₁⟩
        have hEq' : p * qs.prod = a₁ * b := by
          have haux : q * (p * qs.prod) = q * (a₁ * b) := by
            calc
              q * (p * qs.prod) = p * (q * qs.prod) := by ac_rfl
              _ = a * b := by
                simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hEq
              _ = (q * a₁) * b := by rw [ha₁]
              _ = q * (a₁ * b) := by ac_rfl
          exact mul_left_cancel₀ hq.ne_zero haux
        rcases ih (a := a₁) (b := b) htail hEq' with ⟨f₁, f₂, a', b', hpart, ha, hb, hpab⟩
        refine ⟨q ::ₘ f₁, f₂, a', b', ?_, ?_, hb, hpab⟩
        · simp [hpart]
        · calc
            a = q * a₁ := ha₁
            _ = q * (f₁.prod * a') := by rw [ha]
            _ = (q ::ₘ f₁).prod * a' := by simp [mul_assoc]
      · rcases hqb with ⟨b₁, hb₁⟩
        have hEq' : p * qs.prod = a * b₁ := by
          have haux : q * (p * qs.prod) = q * (a * b₁) := by
            calc
              q * (p * qs.prod) = p * (q * qs.prod) := by ac_rfl
              _ = a * b := by
                simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hEq
              _ = a * (q * b₁) := by rw [hb₁]
              _ = q * (a * b₁) := by ac_rfl
          exact mul_left_cancel₀ hq.ne_zero haux
        rcases ih (a := a) (b := b₁) htail hEq' with ⟨f₁, f₂, a', b', hpart, ha, hb, hpab⟩
        refine ⟨f₁, q ::ₘ f₂, a', b', ?_, ha, ?_, hpab⟩
        · simp [hpart]
        · calc
            b = q * b₁ := hb₁
            _ = q * (f₂.prod * b') := by rw [hb]
            _ = (q ::ₘ f₂).prod * b' := by simp [mul_assoc]
  exact hmain f a b hf hEq
end NagataFactoriality
