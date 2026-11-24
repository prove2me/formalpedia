-- Prove2me | solution 1 for GlobalTheory.Lyndon.interleaves_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:53:22.475798+00:00
-- url     : https://prove2.me/submissions/00cfc935-9d3f-4934-9a17-4d0d9dddac7c

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
theorem _root_.solution (w : List A) : ∀ (x y : List A) (S : Multiset (List A)),
    Interleaves w ((x ++ y) ::ₘ S) → Interleaves w (x ::ₘ y ::ₘ S) := by
  induction w with
  | nil => intro x y S h; simp [Interleaves] at h ⊢; tauto
  | cons a w ih =>
    rintro x y S ⟨u, T, e, h⟩
    rcases Multiset.cons_eq_cons.1 e with ⟨e1, e2⟩ | ⟨_, R, e1, e2⟩
    · subst e2
      cases x with
      | nil =>
        simp at e1; subst e1
        rw [interleaves_nil_cons]; exact ⟨u, S, rfl, h⟩
      | cons b x =>
        simp at e1
        obtain ⟨rfl, rfl⟩ := e1
        exact ⟨x, _, rfl, ih _ _ _ h⟩
    · subst e1 e2
      rw [Multiset.cons_swap] at h
      refine ⟨u, x ::ₘ y ::ₘ R, ?_, ?_⟩
      · rw [Multiset.cons_swap y, Multiset.cons_swap x]
      · rw [Multiset.cons_swap u, Multiset.cons_swap u]; exact ih _ _ _ h
end GlobalTheory.Lyndon
