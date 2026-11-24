-- Prove2me | solution 1 for GlobalTheory.Lyndon.flatten_mem_shuffleList
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:01:35.976491+00:00
-- url     : https://prove2.me/submissions/e98fbc91-4689-4f12-a656-9d7890e26cbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Shuffle_append_mem_shuffle

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
theorem _root_.solution (L : List (List A)) : L.flatten ∈ shuffleList L := by
  induction L with
  | nil => simp [shuffleList]
  | cons u L ih => exact Multiset.mem_bind.2 ⟨_, ih, append_mem_shuffle _ _⟩
end GlobalTheory.Lyndon
