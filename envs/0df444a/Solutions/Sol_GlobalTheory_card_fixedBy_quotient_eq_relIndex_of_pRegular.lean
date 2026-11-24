-- Prove2me | solution 1 for GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:44:53.188688+00:00
-- url     : https://prove2.me/submissions/3c780c66-8d27-4c87-8dab-a7ca106e7777

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByQuotientEqRelIndexOfPRegular
import Theorems.Thm_GlobalTheory_conj_mem_zpowers_of_mem_of_pRegular

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
theorem _root_.solution :
    ∀ (G : Type) [Group G] [Finite G] (c : G) (p : ℕ) (H N : Subgroup G), Nat.Coprime (orderOf c) p → Subgroup.zpowers c ≤ H → (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) → (∀ g : G, g ∈ N ↔ ∀ d ∈ Subgroup.zpowers c, g * d * g⁻¹ ∈ Subgroup.zpowers c) → Nat.card (MulAction.fixedBy (G ⧸ H) c) = H.relIndex N := by
  intro G _ _ c p H N hc hH hp hN
  have key : ∀ g : G, c • (g : G ⧸ H) = (g : G ⧸ H) ↔ g ∈ N := by
    intro g
    have h1 : c • (g : G ⧸ H) = (g : G ⧸ H) ↔ g⁻¹ * c * g ∈ H := by
      rw [eq_comm, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mul_assoc]
    rw [h1]
    constructor
    · intro hg
      have hy := conj_mem_zpowers_of_mem_of_pRegular c p H hc hp g hg
      rw [← N.inv_mem_iff, hN]
      rintro d ⟨n, rfl⟩
      have h2 := Subgroup.zpow_mem _ hy n
      have h3 : (g⁻¹ * c * g) ^ n = g⁻¹ * c ^ n * g⁻¹⁻¹ := by
        rw [← conj_zpow, inv_inv]
      rw [h3] at h2
      exact h2
    · intro hg
      have := (hN _).1 (N.inv_mem hg) c (Subgroup.mem_zpowers c)
      rw [inv_inv] at this
      exact hH this
  let f : N ⧸ H.subgroupOf N → MulAction.fixedBy (G ⧸ H) c :=
    Quotient.lift (fun n : N => ⟨((n : G) : G ⧸ H), (key n).2 n.2⟩) (by
      intro a b hab
      apply Subtype.ext
      have h : a⁻¹ * b ∈ H.subgroupOf N := QuotientGroup.leftRel_apply.1 hab
      exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using h))
  have hf : Function.Bijective f := by
    constructor
    · intro x y
      induction x using QuotientGroup.induction_on with
      | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
      intro hab
      have h : ((a : G) : G ⧸ H) = ((b : G) : G ⧸ H) := congrArg Subtype.val hab
      rw [QuotientGroup.eq] at h ⊢
      simpa [Subgroup.mem_subgroupOf] using h
    · rintro ⟨x, hx⟩
      induction x using QuotientGroup.induction_on with
      | H g => exact ⟨((⟨g, (key g).1 hx⟩ : N) : N ⧸ H.subgroupOf N), rfl⟩
  exact (Nat.card_eq_of_bijective f hf).symm
end GlobalTheory
