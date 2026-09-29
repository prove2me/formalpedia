-- Prove2me | solution 1 for Ihara.ker_inf_commutator_eq_bot_of_dicyclic_closure_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/46d52dee-8f1e-536c-8ed7-e63bac70d7b4

import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_ker_inf_commutator_eq_bot_of_dicyclic_closure_pair

namespace SolW1a

open Subgroup

open scoped commutatorElement

section Dicyclic

variable {E Q : Type*} [Group E] [Group Q]

private theorem mem_normalizer_zpowers_of_conj {x g : E} {ε : ℤ} (hx : x * g * x⁻¹ = g ^ ε)
    (hx' : x⁻¹ * g * x = g ^ ε) : x ∈ normalizer ((zpowers g : Subgroup E) : Set E) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨j, rfl⟩
    rw [← conj_zpow, hx, ← zpow_mul]
    exact zpow_mem (mem_zpowers g) _
  · intro hmem
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
    have hh : h = x⁻¹ * (g ^ j) * x⁻¹⁻¹ := by rw [hj]; group
    rw [hh, ← conj_zpow, inv_inv, hx', ← zpow_mul]
    exact zpow_mem (mem_zpowers g) _

private theorem ker_inf_commutator_eq_bot_of_dicyclic (π : E →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center E) {a b : Q} {t : ℕ} (hgen : closure ({a, b} : Set Q) = ⊤)
    (hconj : b * a * b⁻¹ = a⁻¹) (hsq : b ^ 2 = a ^ t) (hord : orderOf a = 2 * t) :
    π.ker ⊓ commutator E = ⊥ := by
  obtain ⟨α, hα⟩ := hπ a
  obtain ⟨β, hβ⟩ := hπ b
  have hcen : ∀ z : E, π z = 1 → ∀ e : E, z * e = e * z := fun z hz e =>
    ((mem_center_iff.mp (hker (by simpa [MonoidHom.mem_ker] using hz))) e).symm

  set k₁ : E := α * (β * α * β⁻¹) with hk₁
  set k₂ : E := (α ^ t)⁻¹ * β ^ 2 with hk₂
  have hk₁π : π k₁ = 1 := by simp [hk₁, hα, hβ, hconj]
  have hk₂π : π k₂ = 1 := by simp [hk₂, hα, hβ, hsq]
  have c₁ := hcen k₁ hk₁π
  have c₂ := hcen k₂ hk₂π
  have hk₁inv : ∀ e : E, k₁⁻¹ * e = e * k₁⁻¹ := fun e =>
    calc k₁⁻¹ * e = k₁⁻¹ * (e * k₁) * k₁⁻¹ := by group
      _ = k₁⁻¹ * (k₁ * e) * k₁⁻¹ := by rw [c₁ e]
      _ = e * k₁⁻¹ := by group
  have hk₂inv : ∀ e : E, k₂⁻¹ * e = e * k₂⁻¹ := fun e =>
    calc k₂⁻¹ * e = k₂⁻¹ * (e * k₂) * k₂⁻¹ := by group
      _ = k₂⁻¹ * (k₂ * e) * k₂⁻¹ := by rw [c₂ e]
      _ = e * k₂⁻¹ := by group
  have hβα : β * α * β⁻¹ = α⁻¹ * k₁ := by rw [hk₁, inv_mul_cancel_left]
  have hαt : α ^ t = β ^ 2 * k₂⁻¹ := by rw [hk₂]; group

  set g : E := α * α * k₁⁻¹ with hg
  have F1 : ⁅α, β⁆ = g := by
    have h1 : β * α⁻¹ * β⁻¹ = k₁⁻¹ * α := by
      calc β * α⁻¹ * β⁻¹ = (β * α * β⁻¹)⁻¹ := by group
        _ = (α⁻¹ * k₁)⁻¹ := by rw [hβα]
        _ = k₁⁻¹ * α := by group
    calc ⁅α, β⁆ = α * (β * α⁻¹ * β⁻¹) := by rw [commutatorElement_def]; group
      _ = α * (k₁⁻¹ * α) := by rw [h1]
      _ = α * (α * k₁⁻¹) := by rw [hk₁inv α]
      _ = g := by rw [hg]; group
  have F3 : α * g * α⁻¹ = g := by
    calc α * g * α⁻¹ = α * α * (α * k₁⁻¹) * α⁻¹ := by rw [hg]; group
      _ = α * α * (k₁⁻¹ * α) * α⁻¹ := by rw [← hk₁inv α]
      _ = g := by rw [hg]; group
  have F3' : α⁻¹ * g * α = g := by
    calc α⁻¹ * g * α = α⁻¹ * (α * g * α⁻¹) * α := by rw [F3]
      _ = g := by group
  have F2 : β * g * β⁻¹ = g⁻¹ := by
    have h2 : β * (α * α) * β⁻¹ = α⁻¹ * α⁻¹ * (k₁ * k₁) := by
      calc β * (α * α) * β⁻¹ = (β * α * β⁻¹) * (β * α * β⁻¹) := by group
        _ = α⁻¹ * k₁ * (α⁻¹ * k₁) := by rw [hβα]
        _ = α⁻¹ * (k₁ * α⁻¹) * k₁ := by group
        _ = α⁻¹ * (α⁻¹ * k₁) * k₁ := by rw [c₁ α⁻¹]
        _ = α⁻¹ * α⁻¹ * (k₁ * k₁) := by group
    calc β * g * β⁻¹ = (β * (α * α) * β⁻¹) * (β * k₁⁻¹ * β⁻¹) := by rw [hg]; group
      _ = α⁻¹ * α⁻¹ * (k₁ * k₁) * (β * k₁⁻¹ * β⁻¹) := by rw [h2]
      _ = α⁻¹ * α⁻¹ * (k₁ * k₁) * (k₁⁻¹ * β * β⁻¹) := by rw [← hk₁inv β]
      _ = α⁻¹ * (α⁻¹ * k₁) := by group
      _ = α⁻¹ * (k₁ * α⁻¹) := by rw [← c₁ α⁻¹]
      _ = (α⁻¹ * k₁) * α⁻¹ := by group
      _ = (k₁ * α⁻¹) * α⁻¹ := by rw [← c₁ α⁻¹]
      _ = g⁻¹ := by rw [hg]; group
  have F2' : β⁻¹ * g * β = g⁻¹ := by
    calc β⁻¹ * g * β = (β⁻¹ * (β * g * β⁻¹) * β)⁻¹ := by rw [F2]; group
      _ = g⁻¹ := by group

  have F4 : g ^ t = 1 := by
    have hβαt : β * α ^ t * β⁻¹ = α ^ t := by
      rw [hαt]
      calc β * (β ^ 2 * k₂⁻¹) * β⁻¹ = β ^ 2 * (β * k₂⁻¹ * β⁻¹) := by group
        _ = β ^ 2 * (k₂⁻¹ * β * β⁻¹) := by rw [← hk₂inv β]
        _ = β ^ 2 * k₂⁻¹ := by group
    have hβαt' : β * α ^ t * β⁻¹ = (α ^ t)⁻¹ * k₁ ^ t := by
      have hc : Commute α⁻¹ k₁ := (c₁ α⁻¹).symm
      rw [← conj_pow, hβα, hc.mul_pow, inv_pow]
    have h2t : α ^ t * α ^ t = k₁ ^ t := by
      have h := hβαt.symm.trans hβαt'
      calc α ^ t * α ^ t = α ^ t * ((α ^ t)⁻¹ * k₁ ^ t) := by rw [← h]
        _ = k₁ ^ t := mul_inv_cancel_left _ _
    have hcomm : Commute (α * α) k₁⁻¹ := (hk₁inv (α * α)).symm
    rw [hg, hcomm.mul_pow, (Commute.refl α).mul_pow, h2t, inv_pow, mul_inv_cancel]

  set S : Set E := {α, β} ∪ (π.ker : Set E) with hS
  have hStop : closure S = ⊤ := by
    rw [eq_top_iff]
    intro e _
    have he : π e ∈ (closure ({α, β} : Set E)).map π := by
      rw [MonoidHom.map_closure, Set.image_pair, hα, hβ, hgen]
      exact mem_top _
    obtain ⟨w, hw, hwe⟩ := he
    have hwe' : w⁻¹ * e ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwe, inv_mul_cancel]
    rw [show e = w * (w⁻¹ * e) by group]
    exact mul_mem (closure_mono Set.subset_union_left hw)
      (subset_closure (Set.mem_union_right _ hwe'))
  have hN : (zpowers g).Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hStop, closure_le]
    rintro x (hx | hx)
    · rcases hx with rfl | rfl
      · exact mem_normalizer_zpowers_of_conj (ε := 1) (by rw [zpow_one, F3]) (by rw [zpow_one, F3'])
      · exact mem_normalizer_zpowers_of_conj (ε := -1) (by rw [zpow_neg, zpow_one, F2])
          (by rw [zpow_neg, zpow_one, F2'])
    · have cx := hcen x (by simpa [MonoidHom.mem_ker] using hx)
      refine mem_normalizer_zpowers_of_conj (ε := 1) ?_ ?_
      · rw [zpow_one, cx g]; group
      · rw [zpow_one, mul_assoc, ← cx g]; group

  have hpair : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ zpowers g := by
    have hz : ∀ z ∈ (π.ker : Set E), ∀ y : E, ⁅z, y⁆ = 1 := fun z hz y => by
      rw [commutatorElement_eq_one_iff_commute]
      exact hcen z (by simpa [MonoidHom.mem_ker] using hz) y
    rintro x (hx | hx) y (hy | hy)
    · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rw [commutatorElement_self]; exact one_mem _
      · rw [F1]; exact mem_zpowers g
      · rw [← commutatorElement_inv, F1]; exact inv_mem (mem_zpowers g)
      · rw [commutatorElement_self]; exact one_mem _
    · rw [← commutatorElement_inv, hz y hy x, inv_one]; exact one_mem _
    · rw [hz x hx y]; exact one_mem _
    · rw [hz x hx y]; exact one_mem _

  have hcommle : commutator E ≤ zpowers g := by
    haveI := hN
    let φ := QuotientGroup.mk' (zpowers g)
    have hS' : ∀ x ∈ φ '' S, ∀ y ∈ φ '' S, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have h1 : φ ⁅x, y⁆ = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr (hpair x hx y hy)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h1
      exact h1.eq
    have htop : closure (φ '' S) = ⊤ := by
      rw [← MonoidHom.map_closure, hStop, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    have hcent : (⊤ : Subgroup (E ⧸ zpowers g)) ≤ centralizer ((⊤ : Subgroup (E ⧸ zpowers g)) : Set _) := by
      have h' : φ '' S ⊆ centralizer (φ '' S) := fun x hx =>
        mem_centralizer_iff.mpr fun y hy => (hS' x hx y hy).symm
      have h'' : closure (φ '' S) ≤ centralizer (φ '' S) := (closure_le _).mpr h'
      rw [← centralizer_closure (φ '' S), htop] at h''
      exact h''
    rw [_root_.commutator_def, commutator_le]
    intro x _ y _
    refine (QuotientGroup.eq_one_iff _).mp ?_
    rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact mem_centralizer_iff.mp (hcent (mem_top (φ y))) (φ x) (mem_top _)

  rw [eq_bot_iff]
  rintro x ⟨hxker, hxcomm⟩
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hcommle hxcomm)
  have hπg : π g = a ^ 2 := by simp [hg, hα, hk₁π, pow_two]
  have hj : (g : E) ^ j ∈ π.ker := hxker
  rw [MonoidHom.mem_ker, map_zpow, hπg, ← zpow_natCast, ← zpow_mul] at hj
  have hdvd : ((orderOf a : ℕ) : ℤ) ∣ ((2 : ℕ) : ℤ) * j := orderOf_dvd_iff_zpow_eq_one.mpr hj
  rw [hord, Nat.cast_mul] at hdvd
  obtain ⟨c, hc⟩ := (mul_dvd_mul_iff_left (by norm_num : ((2 : ℕ) : ℤ) ≠ 0)).mp hdvd
  rw [mem_bot, hc, zpow_mul, zpow_natCast, F4, one_zpow]

end Dicyclic

end SolW1a

open Subgroup in

theorem solution {G : Type*} [Group G] {a b : G}
    {t : ℕ} (hconj : b * a * b⁻¹ = a⁻¹) (hsq : b ^ 2 = a ^ t) (hord : orderOf a = 2 * t)
    {E : Type*} [Group E] (π : E →* closure ({a, b} : Set G)) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) : π.ker ⊓ commutator E = ⊥ := by
  have ha : a ∈ closure ({a, b} : Set G) := subset_closure (by simp)
  have hb : b ∈ closure ({a, b} : Set G) := subset_closure (by simp)
  refine SolW1a.ker_inf_commutator_eq_bot_of_dicyclic π hπ hcen
    (a := (⟨a, ha⟩ : closure ({a, b} : Set G))) (b := ⟨b, hb⟩) (t := t) ?_
    (Subtype.ext (by simp [hconj])) (Subtype.ext (by simp [hsq])) ?_
  · have h : ({⟨a, ha⟩, ⟨b, hb⟩} : Set (closure ({a, b} : Set G))) =
        ((↑) : closure ({a, b} : Set G) → G) ⁻¹' {a, b} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]
    rw [h]
    exact closure_closure_coe_preimage
  · rw [Subgroup.orderOf_mk, hord]

end S_Ihara_ker_inf_commutator_eq_bot_of_dicyclic_closure_pair
end P2MW
export P2MW.S_Ihara_ker_inf_commutator_eq_bot_of_dicyclic_closure_pair (solution)
