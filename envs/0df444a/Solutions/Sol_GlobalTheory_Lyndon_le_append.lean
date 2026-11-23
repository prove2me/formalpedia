-- Prove2me | solution 1 for GlobalTheory.Lyndon.le_append
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:29.001806+00:00
-- url     : https://prove2.me/submissions/abd1e958-44ac-4566-a59c-aea4eda06b38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_append_lt_append_left
import Theorems.Thm_GlobalTheory_Lyndon_nil_le

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
theorem _root_.solution (p u : List A) : p ≤ p ++ u := by
  rcases (nil_le u).lt_or_eq with h | h
  · simpa using (append_lt_append_left p h).le
  · simp [← h]
end GlobalTheory.Lyndon
