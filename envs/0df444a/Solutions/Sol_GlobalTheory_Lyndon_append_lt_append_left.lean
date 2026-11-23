-- Prove2me | solution 1 for GlobalTheory.Lyndon.append_lt_append_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:05.253536+00:00
-- url     : https://prove2.me/submissions/81c02fd6-106e-422c-8a0e-a26d75ca6aa7

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
namespace GlobalTheory.Lyndon
theorem _root_.solution (p : List A) {u v : List A} (h : u < v) : p ++ u < p ++ v := by
  induction p with
  | nil => exact h
  | cons a p ih => exact List.Lex.cons ih
end GlobalTheory.Lyndon
