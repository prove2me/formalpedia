-- Prove2me | solution 1 for GlobalTheory.Lyndon.append_lt_of_lt_of_length
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:45.294445+00:00
-- url     : https://prove2.me/submissions/788c5cf9-c550-405f-bfef-96f6c4717144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_lt_cases

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
theorem _root_.solution {u v : List A} (h : u < v) (hl : v.length ≤ u.length)
    (x y : List A) : u ++ x < v ++ y := by
  rcases lt_cases h with h | ⟨t, ht, rfl⟩
  · exact h x y
  · exact absurd (by simpa using hl) ht
end GlobalTheory.Lyndon
