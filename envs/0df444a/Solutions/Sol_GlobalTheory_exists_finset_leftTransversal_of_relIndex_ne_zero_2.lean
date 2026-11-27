-- Prove2me | solution 2 for GlobalTheory.exists_finset_leftTransversal_of_relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:58.473821+00:00
-- url     : https://prove2.me/submissions/5e1fe9de-9700-4290-90ae-7e9f88da64bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetLeftTransversalOfRelIndexNeZero

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
theorem _root_.solution : ∀ {G : Type} [Group G] (H K : Subgroup G),
    K ≤ H → K.relIndex H ≠ 0 → ∃ R : Finset G, (∀ r ∈ R, r ∈ H) ∧ ∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K := by
  intro G _ H K _ hrel
  have hfin : Finite (H ⧸ K.subgroupOf H) := by
    apply Nat.finite_of_card_ne_zero
    simpa [Subgroup.relIndex, Subgroup.index] using hrel
  let f : H ⧸ K.subgroupOf H → G := fun q => ((Quotient.out q : H) : G)
  have hR : (Set.range f).Finite := Set.finite_range f
  refine ⟨hR.toFinset, ?_, ?_⟩
  · intro r hr
    rw [Set.Finite.mem_toFinset] at hr
    obtain ⟨q, rfl⟩ := hr
    exact (Quotient.out q : H).2
  · intro k hk
    refine ⟨f (QuotientGroup.mk (⟨k, hk⟩ : H)), ⟨?_, ?_⟩, ?_⟩
    · rw [Set.Finite.mem_toFinset]; exact ⟨_, rfl⟩
    · have h1 : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : H) : H ⧸ K.subgroupOf H)) :
          H ⧸ K.subgroupOf H) = QuotientGroup.mk ⟨k, hk⟩ := QuotientGroup.out_eq' _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      simpa [f] using h1
    · rintro r ⟨hr, hrk⟩
      rw [Set.Finite.mem_toFinset] at hr
      obtain ⟨q, rfl⟩ := hr
      have h2 : (QuotientGroup.mk (Quotient.out q) : H ⧸ K.subgroupOf H) = QuotientGroup.mk ⟨k, hk⟩ := by
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [f] using hrk
      rw [QuotientGroup.out_eq'] at h2
      simp [f, h2]
end GlobalTheory
