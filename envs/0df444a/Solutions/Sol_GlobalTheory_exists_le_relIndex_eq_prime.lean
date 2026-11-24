-- Prove2me | solution 1 for GlobalTheory.exists_le_relIndex_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:43.724507+00:00
-- url     : https://prove2.me/submissions/3f392e1c-b807-4106-a5e7-a6de2abeed27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {M : Type*} [AddCommGroup M]
namespace GlobalTheory
theorem _root_.solution {p : ℕ} (hp : p.Prime) (H : AddSubgroup M)
    (h0 : H.index ≠ 0) (hd : p ∣ H.index) :
    ∃ K : AddSubgroup M, H ≤ K ∧ H.relIndex K = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : H.FiniteIndex := ⟨h0⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := M ⧸ H) p hd
  refine ⟨(AddSubgroup.zmultiples x).comap (QuotientAddGroup.mk' H), ?_, ?_⟩
  · intro y hy
    simp only [AddSubgroup.mem_comap, QuotientAddGroup.mk'_apply]
    rw [(QuotientAddGroup.eq_zero_iff y).2 hy]
    exact zero_mem _
  · have h1 : H = (⊥ : AddSubgroup (M ⧸ H)).comap (QuotientAddGroup.mk' H) := by
      ext y; simp
    have h2 := AddSubgroup.relIndex_comap (⊥ : AddSubgroup (M ⧸ H)) (QuotientAddGroup.mk' H)
      ((AddSubgroup.zmultiples x).comap (QuotientAddGroup.mk' H))
    rw [← h1, AddSubgroup.map_comap_eq_self_of_surjective (QuotientAddGroup.mk'_surjective H),
      AddSubgroup.relIndex_bot_left, Nat.card_zmultiples, hx] at h2
    exact h2
end GlobalTheory
