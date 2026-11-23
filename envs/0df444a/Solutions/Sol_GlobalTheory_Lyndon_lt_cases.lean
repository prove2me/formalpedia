-- Prove2me | solution 1 for GlobalTheory.Lyndon.lt_cases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:14.132844+00:00
-- url     : https://prove2.me/submissions/9e9d3084-8298-460c-9482-9be73304647f

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
theorem _root_.solution {u v : List A} (h : u < v) :
    (∀ x y, u ++ x < v ++ y) ∨ ∃ t, t ≠ [] ∧ v = u ++ t := by
  have h' : List.Lex (· < ·) u v := h
  clear h
  induction h' with
  | nil => exact Or.inr ⟨_, by simp, rfl⟩
  | rel h => exact Or.inl fun x y => List.Lex.rel h
  | cons _ ih =>
    rcases ih with ih | ⟨t, ht, rfl⟩
    · exact Or.inl fun x y => List.Lex.cons (ih x y)
    · exact Or.inr ⟨t, ht, rfl⟩
end GlobalTheory.Lyndon
