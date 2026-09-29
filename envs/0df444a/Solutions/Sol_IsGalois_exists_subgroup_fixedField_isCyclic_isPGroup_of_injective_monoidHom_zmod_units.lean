-- Prove2me | solution 1 for IsGalois.exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/07ddc758-7df7-529d-aea8-fbc62fc35281

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsGalois_exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace IsGalois
p2m_export "IsGalois" "normalAutEquivQuotient mk"
namespace CycLayerAux
p2m_open "IsGalois"

open scoped Classical

section units

variable (p k : ℕ) [hp : Fact p.Prime]

scoped instance neZero_pow : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩

noncomputable def T : Subgroup (ZMod (p ^ k))ˣ :=
  if p = 2 then Subgroup.zpowers (-1) else (powMonoidHom (p - 1)).ker

theorem T_of_two (h : p = 2) : T p k = Subgroup.zpowers (-1) := if_pos h
theorem T_of_ne_two (h : p ≠ 2) : T p k = (powMonoidHom (p - 1)).ker := if_neg h

theorem neg_one_mem_T : (-1 : (ZMod (p ^ k))ˣ) ∈ T p k := by
  by_cases h : p = 2
  · rw [T_of_two p k h]; exact Subgroup.mem_zpowers _
  · rw [T_of_ne_two p k h, MonoidHom.mem_ker, powMonoidHom_apply]
    have hodd : Odd p := hp.out.odd_of_ne_two h
    obtain ⟨m, hm⟩ := hodd
    rw [hm, Nat.add_sub_cancel, pow_mul, neg_one_sq, one_pow]

theorem card_units_dvd : Nat.card (ZMod (p ^ k))ˣ ∣ p ^ k * (p - 1) := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Nat.totient_prime_pow hp.out hk]
    exact Nat.mul_dvd_mul_right (pow_dvd_pow p (Nat.sub_le k 1)) _

theorem pow_pow_mul_eq_one (x : (ZMod (p ^ k))ˣ) : x ^ (p ^ k * (p - 1)) = 1 := by
  obtain ⟨c, hc⟩ := card_units_dvd p k
  rw [hc, pow_mul, pow_card_eq_one', one_pow]

theorem pow_mem_T (x : (ZMod (p ^ k))ˣ) : x ^ (p ^ k) ∈ T p k := by
  by_cases h : p = 2
  · have h1 := pow_pow_mul_eq_one p k x
    subst h
    norm_num at h1
    rw [h1]
    exact Subgroup.one_mem _
  · rw [T_of_ne_two p k h, MonoidHom.mem_ker, powMonoidHom_apply, ← pow_mul]
    exact pow_pow_mul_eq_one p k x

theorem card_T_le : Nat.card (T p k) ≤ 2 * (p - 1) := by
  by_cases h : p = 2
  · rw [T_of_two p k h, Nat.card_zpowers, h]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [neg_one_sq])
  · haveI : IsCyclic (ZMod (p ^ k))ˣ := ZMod.isCyclic_units_of_prime_pow p hp.out h k
    have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
    have key := IsCyclic.card_pow_eq_one_le (α := (ZMod (p ^ k))ˣ) hp1
    have hcard : Nat.card (T p k) = (Finset.univ.filter fun a : (ZMod (p ^ k))ˣ => a ^ (p - 1) = 1).card := by
      rw [T_of_ne_two p k h, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun x => by rw [MonoidHom.mem_ker, powMonoidHom_apply])
    rw [hcard]
    exact key.trans (by omega)

theorem eq_or_eq_of_mem_zpowers_neg_one {G : Type} [Group G] [HasDistribNeg G] {x : G} (hx : x ∈ Subgroup.zpowers (-1 : G)) :
    x = 1 ∨ x = -1 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rcases Int.even_or_odd j with hj | hj
  · left; exact hj.neg_one_zpow
  · right; exact hj.neg_one_zpow

theorem isCyclic_quot_two (n : ℕ) : IsCyclic ((ZMod (2 ^ (n + 2)))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) := by
  have h5 : Nat.Coprime 5 (2 ^ (n + 2)) := Nat.Coprime.pow_right _ (by norm_num)
  set u5 : (ZMod (2 ^ (n + 2)))ˣ := ZMod.unitOfCoprime 5 h5 with hu5
  have hcoe : ((u5 : (ZMod (2 ^ (n + 2)))ˣ) : ZMod (2 ^ (n + 2))) = 5 := by
    rw [hu5, ZMod.coe_unitOfCoprime]; norm_num
  have hord : orderOf u5 = 2 ^ n := by rw [← orderOf_units, hcoe, ZMod.orderOf_five]
  set Tm : Subgroup (ZMod (2 ^ (n + 2)))ˣ := Subgroup.zpowers (-1) with hTm
  let f : Subgroup.zpowers u5 →* (ZMod (2 ^ (n + 2)))ˣ ⧸ Tm := (QuotientGroup.mk' Tm).comp (Subgroup.zpowers u5).subtype

  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    rintro ⟨x, hx⟩ hxk
    rw [MonoidHom.mem_ker] at hxk
    change QuotientGroup.mk (s := Tm) x = 1 at hxk
    rw [QuotientGroup.eq_one_iff] at hxk
    apply Subtype.ext
    change x = 1
    rcases eq_or_eq_of_mem_zpowers_neg_one hxk with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx

      have h4 : (4 : ℕ) ∣ 2 ^ (n + 2) := ⟨2 ^ n, by ring⟩
      let π : ZMod (2 ^ (n + 2)) →+* ZMod 4 := ZMod.castHom h4 (ZMod 4)
      have hπ5 : Units.map (π : ZMod (2 ^ (n + 2)) →* ZMod 4) u5 = 1 := by
        apply Units.ext
        rw [Units.coe_map, MonoidHom.coe_coe, hcoe, Units.val_one, map_ofNat]
        decide
      have h2 := congrArg (Units.map (π : ZMod (2 ^ (n + 2)) →* ZMod 4)) h1
      rw [map_zpow, hπ5, one_zpow] at h2
      have h3 := congrArg Units.val h2
      rw [Units.val_one, Units.coe_map, MonoidHom.coe_coe, Units.val_neg, Units.val_one, map_neg, map_one] at h3
      exact absurd h3 (by decide)

  have hcardU : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ (n + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  have hcardT : Nat.card Tm = 2 := by
    rw [hTm, Nat.card_zpowers, ← orderOf_units, Units.val_neg, Units.val_one]
    have h22 : 2 ^ 2 ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    haveI : Fact (1 < 2 ^ (n + 2)) := ⟨by omega⟩
    rw [orderOf_neg_one, if_neg]
    rw [ZMod.ringChar_zmod_n]
    omega
  have hcardQ : Nat.card ((ZMod (2 ^ (n + 2)))ˣ ⧸ Tm) = 2 ^ n := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Tm
    rw [hcardU, hcardT, pow_succ] at h
    omega
  have hcard5 : Nat.card (Subgroup.zpowers u5) = 2 ^ n := by rw [Nat.card_zpowers, hord]
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by rw [hcardQ, hcard5])
  exact isCyclic_of_surjective f hbij.2

theorem isCyclic_quot_T : IsCyclic ((ZMod (p ^ k))ˣ ⧸ T p k) := by
  by_cases h : p = 2
  · rw [T_of_two p k h]
    subst h
    rcases Nat.lt_or_ge k 2 with hk | hk
    ·
      have hc : Nat.card (ZMod (2 ^ k))ˣ = 1 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
        interval_cases k <;> decide
      haveI : Subsingleton (ZMod (2 ^ k))ˣ := (Nat.card_eq_one_iff_unique.1 hc).1
      exact isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
      exact isCyclic_quot_two n
  · haveI : IsCyclic (ZMod (p ^ k))ˣ := ZMod.isCyclic_units_of_prime_pow p hp.out h k
    rw [T_of_ne_two p k h]
    exact isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

end units

end IsGalois.CycLayerAux
p2m_reactivate "P2MW.S_IsGalois_exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units.IsGalois P2MW.S_IsGalois_exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units.IsGalois.CycLayerAux"
p2m_reactivate "P2MW.S_IsGalois_exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units.IsGalois"

theorem solution
    (E C : Type) [Field E] [Field C] [Algebra E C] [FiniteDimensional E C] [IsGalois E C]
    (p k : ℕ) [Fact p.Prime] (χ : (C ≃ₐ[E] C) →* (ZMod (p ^ k))ˣ) (hχ : Function.Injective χ) :
    ∃ (M : Subgroup (C ≃ₐ[E] C)) (_ : M.Normal),
      (∀ g : C ≃ₐ[E] C, χ g = -1 → g ∈ M) ∧
      Nat.card M ≤ 2 * (p - 1) ∧
      IsGalois E (IntermediateField.fixedField M) ∧
      IsCyclic ((IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M)) ∧
      IsPGroup p ((IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M)) ∧
      Nat.card ((IntermediateField.fixedField M) ≃ₐ[E] (IntermediateField.fixedField M)) * Nat.card M = Nat.card (C ≃ₐ[E] C) := by
  classical
  let ψ : (C ≃ₐ[E] C) →* (ZMod (p ^ k))ˣ ⧸ IsGalois.CycLayerAux.T p k := (QuotientGroup.mk' _).comp χ
  have hmem : ∀ g, g ∈ ψ.ker ↔ χ g ∈ IsGalois.CycLayerAux.T p k := fun g => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  haveI : ψ.ker.Normal := inferInstance

  haveI : IsCyclic ((ZMod (p ^ k))ˣ ⧸ IsGalois.CycLayerAux.T p k) := IsGalois.CycLayerAux.isCyclic_quot_T p k
  have hcycQ : IsCyclic ((C ≃ₐ[E] C) ⧸ ψ.ker) := isCyclic_of_injective _ (QuotientGroup.kerLift_injective ψ)
  have hpQ : IsPGroup p ((C ≃ₐ[E] C) ⧸ ψ.ker) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hmem, map_pow]
      exact IsGalois.CycLayerAux.pow_mem_T p k (χ g)
  let e := IsGalois.normalAutEquivQuotient ψ.ker
  refine ⟨ψ.ker, inferInstance, ?_, ?_, inferInstance, ?_, ?_, ?_⟩
  · intro g hg
    rw [hmem, hg]
    exact IsGalois.CycLayerAux.neg_one_mem_T p k
  ·
    refine le_trans ?_ (IsGalois.CycLayerAux.card_T_le p k)
    refine Nat.card_le_card_of_injective (fun g : ψ.ker => (⟨χ g, (hmem g).1 g.2⟩ : IsGalois.CycLayerAux.T p k)) ?_
    intro a b h
    exact Subtype.ext (hχ (congrArg Subtype.val h))
  · exact isCyclic_of_surjective e e.surjective
  · exact hpQ.of_equiv e
  · rw [Nat.card_congr e.toEquiv.symm]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker).symm

end S_IsGalois_exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units
end P2MW
export P2MW.S_IsGalois_exists_subgroup_fixedField_isCyclic_isPGroup_of_injective_monoidHom_zmod_units (solution)
