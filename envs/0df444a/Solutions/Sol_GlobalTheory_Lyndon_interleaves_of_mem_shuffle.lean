-- Prove2me | solution 1 for GlobalTheory.Lyndon.interleaves_of_mem_shuffle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:53:21.62587+00:00
-- url     : https://prove2.me/submissions/588d10c8-d5dc-44a7-8b24-a4ac72a9a3c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_interleaves_nil_cons

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
omit [LinearOrder A]
namespace GlobalTheory.Lyndon
theorem _root_.solution : ∀ (u x w : List A) (S : Multiset (List A)),
    w ∈ shuffle u x → Interleaves x S → Interleaves w (u ::ₘ S)
  | [], x, w, S, h, hS => by
      simp at h; subst h; exact (interleaves_nil_cons _ _).2 hS
  | a :: u, [], w, S, h, hS => by
      simp at h; subst h
      exact ⟨u, S, rfl, solution u [] u S (by simp) hS⟩
  | a :: u, b :: v, w, S, h, hS => by
      rw [shuffle_cons_cons, Multiset.mem_add, Multiset.mem_map, Multiset.mem_map] at h
      rcases h with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · exact ⟨u, S, rfl, solution u (b :: v) y S hy hS⟩
      · obtain ⟨t, T, rfl, hT⟩ := hS
        refine ⟨t, (a :: u) ::ₘ T, Multiset.cons_swap _ _ _, ?_⟩
        rw [Multiset.cons_swap]
        exact solution (a :: u) v y _ hy hT
termination_by u x => u.length + x.length
end GlobalTheory.Lyndon
