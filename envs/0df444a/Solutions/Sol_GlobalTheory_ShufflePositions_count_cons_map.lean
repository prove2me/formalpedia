-- Prove2me | solution 1 for GlobalTheory.ShufflePositions.count_cons_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:10.301661+00:00
-- url     : https://prove2.me/submissions/324d2685-2986-45c1-9b28-9f1dc66ac9d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CountBindWordShuffleByPositions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory
open GlobalTheory.ShufflePositions
variable {A : Type} [DecidableEq A]
namespace GlobalTheory.ShufflePositions
theorem _root_.solution (a b : A) (x : List A) (s : Multiset (List A)) :
    (s.map (List.cons b)).count (a :: x) = if a = b then s.count x else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    exact Multiset.count_map_eq_count' (List.cons a) s List.cons_injective x
  · rw [if_neg hab, Multiset.count_eq_zero]
    intro hmem
    obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 hmem
    exact hab (List.cons.inj hy).1.symm
end GlobalTheory.ShufflePositions
