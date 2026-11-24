-- Prove2me | solution 1 for GlobalTheory.Lyndon.exists_factors_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:13:30.294783+00:00
-- url     : https://prove2.me/submissions/3e2fe484-d4d6-496e-933e-a44bbaa77f91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_isLyndon_append
import Theorems.Thm_GlobalTheory_Lyndon_IsFactors_tail

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
    ∀ l, IsLyndon l → ∃ L', IsFactors L' ∧ L'.flatten = l ++ L.flatten := by
  induction L with
  | nil => exact fun l hl => ⟨[l], ⟨by simpa using hl, by simp⟩, by simp⟩
  | cons m L ih =>
    intro l hl
    rcases le_or_gt m l with h | h
    · refine ⟨l :: m :: L, ⟨?_, List.pairwise_cons.2 ⟨?_, hL.2⟩⟩, by simp⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hl
        · exact hL.1 x hx
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h
        · exact le_trans ((List.pairwise_cons.1 hL.2).1 x hx) h
    · obtain ⟨L', h1, h2⟩ := ih hL.tail (l ++ m) (isLyndon_append hl (hL.1 m (by simp)) h)
      exact ⟨L', h1, by simp [h2]⟩
end GlobalTheory.Lyndon
