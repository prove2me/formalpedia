-- Prove2me | solution 1 for GlobalTheory.exists_sylow_over_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:46:57.235938+00:00
-- url     : https://prove2.me/submissions/e85af182-c9a1-49b6-b3a0-1531308e02a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsSylowOverSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (G : Type) [Group G] [Finite G] (C : Subgroup G) (p : ℕ)
    (hp : p.Prime) :
    ∃ H : Subgroup G, C ≤ H ∧ (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧
      (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ C) ∧
      ∀ N : Subgroup G, (∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C) → ¬ p ∣ H.relIndex N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let N : Subgroup G :=
    { carrier := {g | ∀ c ∈ C, g * c * g⁻¹ ∈ C}
      one_mem' := by intro c hc; simpa using hc
      mul_mem' := by
        intro a b ha hb c hc
        have := ha _ (hb c hc)
        simpa [mul_assoc] using this
      inv_mem' := by
        intro a ha c hc
        have key : ∀ n : ℕ, ∀ c ∈ C, a ^ n * c * (a ^ n)⁻¹ ∈ C := by
          intro n
          induction n with
          | zero => intro c hc; simpa using hc
          | succ n ih =>
            intro c hc
            have := ha _ (ih c hc)
            simpa [pow_succ', mul_assoc] using this
        have h1 : a ^ (orderOf a - 1) = a⁻¹ := by
          have hpos : 0 < orderOf a := orderOf_pos a
          apply eq_inv_of_mul_eq_one_left
          rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        have := key (orderOf a - 1) c hc
        rwa [h1] at this }
  have hN : ∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C := fun g => Iff.rfl
  let C' : Subgroup N := C.subgroupOf N
  haveI hC' : C'.Normal := ⟨fun n hn g => by
    simp only [C', Subgroup.mem_subgroupOf] at hn ⊢
    exact (hN g).1 g.2 _ hn⟩
  let P : Sylow p (N ⧸ C') := Classical.arbitrary _
  let H' : Subgroup N := (P : Subgroup (N ⧸ C')).comap (QuotientGroup.mk' C')
  refine ⟨H'.map N.subtype, ?_, ?_, ?_, ?_⟩
  · intro c hc
    have hcN : c ∈ N := (hN c).2 fun d hd => C.mul_mem (C.mul_mem hc hd) (C.inv_mem hc)
    refine ⟨⟨c, hcN⟩, ?_, rfl⟩
    have : QuotientGroup.mk' C' ⟨c, hcN⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc
    change QuotientGroup.mk' C' ⟨c, hcN⟩ ∈ (P : Subgroup (N ⧸ C'))
    rw [this]
    exact one_mem _
  · rintro _ ⟨h, -, rfl⟩
    exact (hN h).1 h.2
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨QuotientGroup.mk' C' h, hh⟩
    refine ⟨k, ?_⟩
    have h2 : QuotientGroup.mk' C' (h ^ p ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  · intro N' hN'
    obtain rfl : N' = N := by
      ext g
      rw [hN', hN]
    have h1 : (H'.map N.subtype).subgroupOf N = H' :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective H'
    rw [Subgroup.relIndex, h1]
    have h2 : H'.index = (P : Subgroup (N ⧸ C')).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective C')
    rw [h2]
    exact P.not_dvd_index
end GlobalTheory
