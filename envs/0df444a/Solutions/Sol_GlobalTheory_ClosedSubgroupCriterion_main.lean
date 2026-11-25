-- Prove2me | solution 1 for GlobalTheory.ClosedSubgroupCriterion.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:32:41.109178+00:00
-- url     : https://prove2.me/submissions/5952e1f5-e4d2-4714-a021-c7e3e1c7ff8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsMore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedSubgroupCriterion
namespace GlobalTheory.ClosedSubgroupCriterion
theorem _root_.solution : ∀ {n j : ℕ} (a : Fin n → ℤ), Antitone a → (∀ (i : Fin n), a i = (0 : ℤ) ∨ a i = (1 : ℤ)) →
    Finset.card {i : Fin n | a i = (1 : ℤ)} = j → ∀ (i : Fin n), a i = (1 : ℤ) ↔ (↑i : ℕ) < j := by
  intro n j a ha h01 hj i
  constructor
  · intro hi
    by_contra hlt
    push_neg at hlt
    have hsub : Finset.Iic i ⊆ ({k : Fin n | a k = (1:ℤ)} : Finset (Fin n)) := by
      intro k hk
      rw [Finset.mem_Iic] at hk
      have := ha hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases h01 k with h | h
      · rw [h, hi] at this; norm_num at this
      · exact h
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic, hj] at this
    omega
  · intro hi
    rcases h01 i with h | h
    · exfalso
      have hsub : ({k : Fin n | a k = (1:ℤ)} : Finset (Fin n)) ⊆ Finset.Iio i := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [Finset.mem_Iio]
        by_contra hle
        push_neg at hle
        have := ha hle
        rw [h, hk] at this; norm_num at this
      have := Finset.card_le_card hsub
      rw [Fin.card_Iio, hj] at this
      omega
    · exact h
end GlobalTheory.ClosedSubgroupCriterion
