-- Prove2me | solution 1 for GlobalTheory.Lyndon.of_mem_shuffleList
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:13:23.588131+00:00
-- url     : https://prove2.me/submissions/537a705f-e645-4cc7-96ed-62a3a49a16b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Shuffle_perm_of_mem_shuffle
import Theorems.Thm_GlobalTheory_Lyndon_interleaves_of_mem_shuffle

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
theorem _root_.solution (L : List (List A)) :
    ∀ w ∈ shuffleList L, w.Perm L.flatten ∧ Interleaves w ↑L := by
  induction L with
  | nil => intro w hw; simp [shuffleList] at hw; subst hw; simp [Interleaves]
  | cons u L ih =>
    intro w hw
    obtain ⟨x, hx, hw⟩ := Multiset.mem_bind.1 hw
    exact ⟨(perm_of_mem_shuffle _ _ _ hw).trans ((ih x hx).1.append_left u),
      interleaves_of_mem_shuffle u x w _ hw (ih x hx).2⟩
end GlobalTheory.Lyndon
