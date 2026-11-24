-- Prove2me | solution 1 for GlobalTheory.Lyndon.isLyndon_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:53:23.202978+00:00
-- url     : https://prove2.me/submissions/c4c22a32-abfc-4d10-8ea8-03b856a9efe5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_lt_of_isLyndon
import Theorems.Thm_GlobalTheory_Lyndon_lt_cases
import Theorems.Thm_GlobalTheory_Lyndon_append_lt_of_lt_of_length
import Theorems.Thm_GlobalTheory_Lyndon_append_lt_append_left

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
theorem _root_.solution {l m : List A} (hl : IsLyndon l) (hm : IsLyndon m) (h : l < m) :
    IsLyndon (l ++ m) := by
  have h0 : l ++ m < m := by
    rcases lt_cases h with h | ⟨t, ht, e⟩
    · simpa using h m []
    · have := append_lt_append_left l (lt_of_isLyndon hm hl.1 ht e)
      rwa [← e] at this
  refine ⟨by simp [hl.1], fun u v hu hv e => ?_⟩
  change l ++ m < v
  rcases List.append_eq_append_iff.1 e with ⟨s, e1, e2⟩ | ⟨s, e1, e2⟩
  · by_cases hs : s = []
    · subst hs; simp at e2; rw [← e2]; exact h0
    · exact h0.trans (lt_of_isLyndon hm hs hv e2)
  · by_cases hs : s = []
    · subst hs; simp at e2; rw [e2]; exact h0
    · rw [e2]
      exact append_lt_of_lt_of_length (lt_of_isLyndon hl hu hs e1) (by simp [e1]) _ _
end GlobalTheory.Lyndon
