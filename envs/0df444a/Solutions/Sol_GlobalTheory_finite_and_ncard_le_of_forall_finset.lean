-- Prove2me | solution 1 for GlobalTheory.finite_and_ncard_le_of_forall_finset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:42.323277+00:00
-- url     : https://prove2.me/submissions/14e1df85-b0d3-416e-a806-ad3694fbf7f0

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
open MeasureTheory Metric
namespace GlobalTheory
theorem _root_.solution {α : Type*} (S : Set α) (B : ℝ)
    (h : ∀ s : Finset α, (s : Set α) ⊆ S → (s.card : ℝ) ≤ B) :
    S.Finite ∧ (S.ncard : ℝ) ≤ B := by
  have hf : S.Finite := by
    by_contra hinf
    obtain ⟨s, hs, hc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊B⌋₊ + 1)
    have h1 := h s hs
    rw [hc] at h1
    have h2 := Nat.lt_floor_add_one B
    push_cast at h1
    linarith
  refine ⟨hf, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hf]
  exact h _ (by simp)
end GlobalTheory
