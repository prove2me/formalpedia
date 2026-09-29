-- Prove2me | solution 1 for Ihara.hasTrivialSchurMultiplier_of_sylow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/cbd7a6b8-d7b3-51da-8244-c612a55a1cf1

import Mathlib
import Definitions.Def_SchurMultiplierTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_hasTrivialSchurMultiplier_of_sylow

open scoped commutatorElement

namespace IharaSylowReduction

theorem commutatorElement_mul_central_left {E : Type*} [Group E] {z : E}
    (hz : z ∈ Subgroup.center E) (a b : E) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hc : ∀ g : E, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hz g
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_assoc a z b, ← hc b]
  group

theorem commutatorElement_mul_central_right {E : Type*} [Group E] {z : E}
    (hz : z ∈ Subgroup.center E) (a b : E) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hc : ∀ g : E, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hz g
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_assoc a (b * z) a⁻¹,
    mul_assoc b z a⁻¹, ← hc a⁻¹]
  group

theorem finite_of_stem {E G : Type*} [Group E] [Group G] [Finite G] (π : E →* G)
    (hπ : Function.Surjective π) (hcent : π.ker ≤ Subgroup.center E)
    (hcomm : π.ker ≤ commutator E) : Finite E := by
  classical
  have hidx : π.ker.FiniteIndex := by
    refine ⟨?_⟩
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπ]
    exact Nat.card_pos.ne'
  haveI hZ : (Subgroup.center E).FiniteIndex :=
    ⟨fun h0 => hidx.1 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le hcent))⟩
  have hcs : (commutatorSet E).Finite := by
    let f : (E ⧸ Subgroup.center E) × (E ⧸ Subgroup.center E) → E :=
      fun q => ⁅q.1.out, q.2.out⁆
    refine (Set.finite_range f).subset ?_
    rintro g ⟨a, b, rfl⟩
    refine ⟨((a : E ⧸ Subgroup.center E), (b : E ⧸ Subgroup.center E)), ?_⟩
    obtain ⟨za, hza⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center E) a
    obtain ⟨zb, hzb⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center E) b
    show ⁅(a : E ⧸ Subgroup.center E).out, (b : E ⧸ Subgroup.center E).out⁆ = ⁅a, b⁆
    rw [hza, hzb, commutatorElement_mul_central_left za.2,
      commutatorElement_mul_central_right zb.2]
  haveI : Finite (commutatorSet E) := hcs.to_subtype
  haveI : Finite (commutator E) := inferInstance
  haveI : Finite π.ker :=
    Finite.of_injective (Subgroup.inclusion hcomm) (Subgroup.inclusion_injective hcomm)
  haveI : Finite (E ⧸ π.ker) := Subgroup.finite_quotient_of_finiteIndex
  exact Finite.of_subgroup_quotient π.ker

theorem central_pow_index_mem_commutator {E : Type*} [Group E]
    (H : Subgroup E) [H.FiniteIndex] {x : E}
    (hcent : x ∈ Subgroup.center E) (hxH : x ∈ H) (hxcomm : x ∈ commutator E) :
    (⟨x, hxH⟩ : ↥H) ^ H.index ∈ commutator ↥H := by
  classical
  have hkey : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * x ^ k * g₀ ∈ H →
      g₀⁻¹ * x ^ k * g₀ = x ^ k := by
    intro k g₀ _
    have hxc : x ^ k ∈ Subgroup.center E := Subgroup.pow_mem _ hcent k
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp hxc g₀, inv_mul_cancel_left]
  have htr := MonoidHom.transfer_eq_pow
    (Abelianization.of : ↥H →* Abelianization ↥H) x hkey
  have hker : MonoidHom.transfer (Abelianization.of : ↥H →* Abelianization ↥H)
      x = 1 :=
    MonoidHom.mem_ker.mp
      (Abelianization.commutator_subset_ker
        (MonoidHom.transfer (Abelianization.of : ↥H →* Abelianization ↥H))
        hxcomm)
  rw [htr] at hker
  have hmem : (⟨x ^ H.index, pow_mem hxH H.index⟩ : ↥H) ∈
      (Abelianization.of : ↥H →* Abelianization ↥H).ker :=
    MonoidHom.mem_ker.mpr hker
  rw [Abelianization.ker_of] at hmem
  have heq : (⟨x, hxH⟩ : ↥H) ^ H.index =
      (⟨x ^ H.index, pow_mem hxH H.index⟩ : ↥H) :=
    Subtype.ext (by simp)
  rw [heq]
  exact hmem

universe u in

theorem eq_one_of_mem_sylow_of_mem_ker {G : Type u} [Group G] [Finite G]
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      Ihara.HasTrivialSchurMultiplier ↥(P : Subgroup G))
    {E : Type u} [Group E] [Finite E] (π : E →* G)
    (hπ : Function.Surjective π) (hcent : π.ker ≤ Subgroup.center E)
    (hcomm : π.ker ≤ commutator E)
    (p : ℕ) [Fact p.Prime] (S : Sylow p E) {x : E} (hxS : x ∈ (S : Subgroup E))
    (hx1 : π x = 1) : x = 1 := by
  classical
  let ρ : ↥(S : Subgroup E) →* ↥((S : Subgroup E).map π) := π.subgroupMap S
  have hρsurj : Function.Surjective ρ := π.subgroupMap_surjective S
  have htriv : Ihara.HasTrivialSchurMultiplier ↥((S : Subgroup E).map π) :=
    h p (S.mapSurjective hπ)

  have hkerπ : ∀ y : ↥(S : Subgroup E), y ∈ ρ.ker → (y : E) ∈ π.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    have := congrArg Subtype.val hy
    simpa [ρ] using this
  have hker_cent : ρ.ker ≤ Subgroup.center _ := by
    intro y hy
    have hyc : (y : E) ∈ Subgroup.center E := hcent (hkerπ y hy)
    rw [Subgroup.mem_center_iff] at hyc ⊢
    intro g
    exact Subtype.ext (hyc g)
  have hker_comm : ρ.ker ≤ commutator _ := by
    intro y hy
    have hyk : (y : E) ∈ π.ker := hkerπ y hy
    have hyc : (y : E) ∈ Subgroup.center E := hcent hyk
    have hycomm : (y : E) ∈ commutator E := hcomm hyk
    have hpow := central_pow_index_mem_commutator (S : Subgroup E) hyc y.2 hycomm

    obtain ⟨k, hk⟩ := S.isPGroup' y
    have hnd : ¬ p ∣ (S : Subgroup E).index := S.not_dvd_index
    have hcop : ((S : Subgroup E).index).Coprime (orderOf y) :=
      (Nat.Coprime.pow_right k
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnd).symm).coprime_dvd_right
        (orderOf_dvd_of_pow_eq_one hk)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem _ hpow m
  have hbot : ρ.ker = ⊥ := htriv _ ρ hρsurj hker_cent hker_comm
  have hxker : (⟨x, hxS⟩ : ↥(S : Subgroup E)) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (by simpa [ρ] using hx1)
  rw [hbot, Subgroup.mem_bot] at hxker
  exact congrArg Subtype.val hxker

end IharaSylowReduction

open IharaSylowReduction in
theorem solution
    {G : Type*} [Group G] [Finite G]
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      Ihara.HasTrivialSchurMultiplier ↥(P : Subgroup G)) :
    Ihara.HasTrivialSchurMultiplier G := by
  intro E _ π hπ hcent hcomm
  classical
  haveI : Finite E := finite_of_stem π hπ hcent hcomm
  refine (Subgroup.eq_bot_iff_forall _).mpr ?_
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  by_contra hne
  have hord : orderOf a ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.mp h1)
  haveI hpp : Fact (orderOf a).minFac.Prime := ⟨Nat.minFac_prime hord⟩
  set p := (orderOf a).minFac with hp
  have hpd : p ∣ orderOf a := Nat.minFac_dvd _
  set b := a ^ (orderOf a / p) with hb_def
  have hb : orderOf b = p := orderOf_pow_orderOf_div (orderOf_pos a).ne' hpd
  have hb1 : π b = 1 := by rw [hb_def, map_pow, ha, one_pow]
  have hpg : IsPGroup p (Subgroup.zpowers b) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    show (b ^ i) ^ p ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hb,
      pow_orderOf_eq_one, one_zpow]
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  have hbS : b ∈ (S : Subgroup E) := hS (Subgroup.mem_zpowers b)
  have hb_one : b = 1 :=
    eq_one_of_mem_sylow_of_mem_ker h π hπ hcent hcomm p S hbS hb1
  rw [hb_one, orderOf_one] at hb
  exact hpp.out.one_lt.ne' hb.symm

end S_Ihara_hasTrivialSchurMultiplier_of_sylow
end P2MW
export P2MW.S_Ihara_hasTrivialSchurMultiplier_of_sylow (solution)
