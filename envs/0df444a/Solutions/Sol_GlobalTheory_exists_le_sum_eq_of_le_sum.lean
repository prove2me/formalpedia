-- Prove2me | solution 1 for GlobalTheory.exists_le_sum_eq_of_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:32.453349+00:00
-- url     : https://prove2.me/submissions/d875d415-84af-4fe7-ac4d-b8b6d1228b43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCutIntoBoundedGroupsFinset

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
theorem _root_.solution (S : Finset ℕ) (e : ℕ → ℕ) :
    ∀ n, n ≤ ∑ k ∈ S, e k →
      ∃ f : ℕ → ℕ, (∀ k, f k ≤ e k) ∧ ∑ k ∈ S, f k = n ∧ ∀ k, k ∉ S → f k = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro n hn
    refine ⟨fun _ => 0, fun _ => Nat.zero_le _, ?_, fun _ _ => rfl⟩
    simp only [Finset.sum_empty] at hn ⊢
    omega
  | insert a S ha ih =>
    intro n hn
    rw [Finset.sum_insert ha] at hn
    obtain ⟨g, hge, hgs, hgo⟩ := ih (min n (∑ k ∈ S, e k)) (min_le_right _ _)
    refine ⟨fun k => if k = a then n - min n (∑ k ∈ S, e k) else g k, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = a
      · subst hk
        simp only [if_true]
        omega
      · simp only [hk, if_false]
        exact hge k
    · rw [Finset.sum_insert ha, if_pos rfl]
      have hS : ∑ k ∈ S, (if k = a then n - min n (∑ k ∈ S, e k) else g k) = ∑ k ∈ S, g k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have : k ≠ a := fun h => ha (h ▸ hk)
        simp only [this, if_false]
      rw [hS, hgs]
      omega
    · intro k hk
      have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
      simp only [hka, if_false]
      exact hgo k hkS
end GlobalTheory
