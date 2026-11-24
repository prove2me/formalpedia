-- Prove2me | solution 1 for GlobalTheory.card_torsion_pow_log_concave
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:20:00.578268+00:00
-- url     : https://prove2.me/submissions/9926ad1c-7600-44d6-9162-7e5b82f64f0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountLogConcavePrimePowers
import Theorems.Thm_GlobalTheory_killedBy_anti
import Theorems.Thm_GlobalTheory_card_eq_card_ker_mul_card_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (M : Type)
    [AddCommGroup M] [Module (𝓞 F) M] (𝔭 : Ideal (𝓞 F)), 𝔭.IsMaximal → ∀ k : ℕ,
    Finite {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} →
    Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ k, a • x = 0} ≤
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 1), a • x = 0} ^ 2 := by
  intro F _ _ M _ _ 𝔭 hmax k hfin
  have hp0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hmax (RingOfIntegers.not_isField F)
  have hp2 : 𝔭 ^ 2 ≠ ⊥ := pow_ne_zero 2 hp0
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.pow_le_self two_ne_zero : 𝔭 ^ 2 ≤ 𝔭) hp2
  have haP : a ∈ 𝔭 := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have key : 𝔭 ^ (k + 2) ⊔ 𝔭 ^ k * Ideal.span {a} = 𝔭 ^ (k + 1) := by
    have e : 𝔭 ^ (k + 1) = 𝔭 ^ k * (𝔭 ^ 2 ⊔ Ideal.span {a}) := by rw [ha, pow_succ]
    rw [e, Ideal.mul_sup, ← pow_add]
  set A := killedBy M (𝔭 ^ (k + 2)) with hA
  set B := killedBy M (𝔭 ^ (k + 1)) with hB
  set C := killedBy M (𝔭 ^ k) with hC
  have eA : Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} = Nat.card A := rfl
  have eB : Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 1), a • x = 0} = Nat.card B := rfl
  have eC : Nat.card {x : M // ∀ a ∈ 𝔭 ^ k, a • x = 0} = Nat.card C := rfl
  rw [eA, eB, eC]
  have hBA : B ≤ A := killedBy_anti M (Ideal.pow_le_pow_right (by omega))
  have hCB : C ≤ B := killedBy_anti M (Ideal.pow_le_pow_right (by omega))
  haveI : Finite A := hfin
  haveI : Finite B := Finite.of_injective _ (AddSubgroup.inclusion_injective hBA)

  have hAB : ∀ x ∈ A, a • x ∈ B := by
    intro x hx b hb
    rw [← mul_smul]
    apply hx
    rw [pow_succ]
    exact Ideal.mul_mem_mul hb haP

  have hiff : ∀ x ∈ A, (a • x ∈ C ↔ x ∈ B) := by
    intro x hx
    constructor
    · intro hax
      have hle : 𝔭 ^ (k + 1) ≤ LinearMap.ker (LinearMap.toSpanSingleton (𝓞 F) M x) := by
        rw [← key]
        apply sup_le
        · intro b hb
          simpa using hx b hb
        · rw [Ideal.mul_le]
          intro r hr s hs
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
          simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
          rw [← mul_assoc, mul_smul]
          exact hax _ (Ideal.mul_mem_right c _ hr)
      intro b hb
      simpa using hle hb
    · intro hxB b hb
      rw [← mul_smul]
      apply hxB
      rw [pow_succ]
      exact Ideal.mul_mem_mul hb haP
  let π : M →+ M ⧸ C := QuotientAddGroup.mk' C
  let g : A →+ M ⧸ C := (π.comp (DistribMulAction.toAddMonoidHom M a)).comp A.subtype
  let h : B →+ M ⧸ C := π.comp B.subtype
  have hg : Nat.card g.ker = Nat.card B := by
    have : g.ker = B.addSubgroupOf A := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, g, π,
        AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, DistribMulAction.toAddMonoidHom_apply,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact hiff x.1 x.2
    rw [this]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hBA).toEquiv
  have hh : Nat.card h.ker = Nat.card C := by
    have : h.ker = C.addSubgroupOf B := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, h, π,
        AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [this]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hCB).toEquiv
  have hrange : g.range ≤ h.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨a • (x : M), hAB x.1 x.2⟩, rfl⟩
  haveI : Finite h.range := Finite.of_surjective _ h.rangeRestrict_surjective
  have hcard : Nat.card g.range ≤ Nat.card h.range :=
    Nat.card_le_card_of_injective _ (AddSubgroup.inclusion_injective hrange)
  have e1 := card_eq_card_ker_mul_card_range g
  have e2 := card_eq_card_ker_mul_card_range h
  rw [hg] at e1
  rw [hh] at e2
  rw [e1, sq]
  nth_rewrite 3 [e2]
  calc Nat.card B * Nat.card g.range * Nat.card C
      ≤ Nat.card B * Nat.card h.range * Nat.card C := by gcongr
    _ = Nat.card B * (Nat.card C * Nat.card h.range) := by ring
end GlobalTheory
