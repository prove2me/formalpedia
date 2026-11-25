-- Prove2me | solution 1 for GlobalTheory.Lyndon.exists_suffix_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:08:16.501382+00:00
-- url     : https://prove2.me/submissions/0f25c2ab-7ee6-4018-911a-270737dd2a3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_le_append

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
theorem _root_.solution (l : List A) (L : List (List A)) (hL : ∀ m ∈ L, m ≤ l) :
    ∀ t r : List A, t ≠ [] → t ++ r = L.flatten → ∃ s q, q ≠ [] ∧ t = s ++ q ∧ q ≤ l := by
  induction L with
  | nil => intro t r ht e; simp [ht] at e
  | cons m L ih =>
    intro t r ht e
    rw [List.flatten_cons] at e
    have hm := hL m (by simp)
    rcases List.append_eq_append_iff.1 e with ⟨s, e1, e2⟩ | ⟨s, e1, e2⟩
    · exact ⟨[], t, ht, rfl, le_trans (e1 ▸ le_append t s) hm⟩
    · by_cases hs : s = []
      · subst hs; simp at e1; exact ⟨[], t, ht, rfl, e1 ▸ hm⟩
      · obtain ⟨s', q, h1, h2, h3⟩ :=
          ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) s r hs e2.symm
        exact ⟨m ++ s', q, h1, by simp [e1, h2], h3⟩
end GlobalTheory.Lyndon
