-- Prove2me | solution 1 for GlobalTheory.Lyndon.exists_suffix_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:11:25.518163+00:00
-- url     : https://prove2.me/submissions/dc9770e6-0bfb-4ca7-a547-ae91a630df3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
namespace GlobalTheory.Lyndon
theorem _root_.solution {F : List (List A)} (hF : IsFactors F) {f : List A} (hf : f ∈ F) :
    ∃ s g, g ≠ [] ∧ F.flatten = s ++ g ∧ g ≤ f := by
  rcases List.eq_nil_or_concat F with rfl | ⟨F', g, rfl⟩
  · simp at hf
  · rw [List.concat_eq_append] at hF hf ⊢
    refine ⟨F'.flatten, g, (hF.1 g (by simp)).1, by simp, ?_⟩
    rcases List.mem_append.1 hf with h | h
    · exact (List.pairwise_append.1 hF.2).2.2 f h g (by simp)
    · simp at h; exact h.ge
end GlobalTheory.Lyndon
