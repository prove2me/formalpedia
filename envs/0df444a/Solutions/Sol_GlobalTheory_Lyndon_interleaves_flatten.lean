-- Prove2me | solution 1 for GlobalTheory.Lyndon.interleaves_flatten
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:13:21.822073+00:00
-- url     : https://prove2.me/submissions/cf91ab1f-4467-4cb7-9c46-5715db23a8d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_interleaves_nil_cons
import Theorems.Thm_GlobalTheory_Lyndon_interleaves_split

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
theorem _root_.solution (w : List A) (F : List (List A)) : ∀ S : Multiset (List A),
    Interleaves w (F.flatten ::ₘ S) → Interleaves w (↑F + S) := by
  induction F with
  | nil => intro S h; simpa [interleaves_nil_cons] using h
  | cons f F ih =>
    intro S h
    have h1 := interleaves_split w _ _ _ h
    rw [Multiset.cons_swap] at h1
    have h2 := ih _ h1
    rwa [Multiset.add_cons, ← Multiset.cons_add, Multiset.cons_coe] at h2
end GlobalTheory.Lyndon
