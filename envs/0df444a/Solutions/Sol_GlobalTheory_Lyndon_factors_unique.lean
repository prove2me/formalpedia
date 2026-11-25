-- Prove2me | solution 1 for GlobalTheory.Lyndon.factors_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:24.105658+00:00
-- url     : https://prove2.me/submissions/3a057705-5e76-40df-aafe-841bd1ac88bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_IsFactors_tail
import Theorems.Thm_GlobalTheory_Lyndon_eq_nil_of_head_append

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
theorem _root_.solution (L : List (List A)) (hL : IsFactors L) :
    ∀ L', IsFactors L' → L.flatten = L'.flatten → L = L' := by
  induction L with
  | nil =>
    intro L' h e
    cases L' with
    | nil => rfl
    | cons m L' => simp [(h.1 m (by simp)).1] at e
  | cons l L ih =>
    intro L' h e
    cases L' with
    | nil => simp [(hL.1 l (by simp)).1] at e
    | cons m L' =>
      simp only [List.flatten_cons] at e
      have : l = m := by
        rcases List.append_eq_append_iff.1 e with ⟨s, e1, e2⟩ | ⟨s, e1, e2⟩
        · have := eq_nil_of_head_append hL (e1 ▸ h.1 m (by simp)) e2
          simp [e1, this]
        · have := eq_nil_of_head_append h (e1 ▸ hL.1 l (by simp)) e2
          simp [e1, this]
      subst this
      rw [ih hL.tail L' h.tail (List.append_cancel_left e)]
end GlobalTheory.Lyndon
