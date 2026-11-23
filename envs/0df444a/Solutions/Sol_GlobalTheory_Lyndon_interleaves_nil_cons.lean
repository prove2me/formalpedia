-- Prove2me | solution 1 for GlobalTheory.Lyndon.interleaves_nil_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:13.871648+00:00
-- url     : https://prove2.me/submissions/32a6d5fa-c814-4ce2-8d45-33f69ffbeb2e

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
omit [LinearOrder A]
namespace GlobalTheory.Lyndon
theorem _root_.solution (w : List A) :
    ∀ S : Multiset (List A), Interleaves w ([] ::ₘ S) ↔ Interleaves w S := by
  induction w with
  | nil => intro S; simp [Interleaves]
  | cons a w ih =>
    intro S
    constructor
    · rintro ⟨u, T, e, h⟩
      rcases Multiset.cons_eq_cons.1 e with ⟨e1, _⟩ | ⟨_, R, e1, e2⟩
      · simp at e1
      · subst e1 e2
        rw [Multiset.cons_swap, ih] at h
        exact ⟨u, R, rfl, h⟩
    · rintro ⟨u, T, rfl, h⟩
      refine ⟨u, [] ::ₘ T, Multiset.cons_swap _ _ _, ?_⟩
      rw [Multiset.cons_swap, ih]; exact h
end GlobalTheory.Lyndon
