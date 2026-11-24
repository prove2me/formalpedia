-- Prove2me | solution 1 for GlobalTheory.Lyndon.prod_word
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:27.404801+00:00
-- url     : https://prove2.me/submissions/80df9785-6be9-41d9-91e4-3dbc0ad898a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_ShuffleAlgebra_word_nil
import Theorems.Thm_GlobalTheory_ShuffleAlgebra_word_mul_word

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
open ShuffleAlgebra
variable (K : Type) [Field K]
omit [LinearOrder A]
namespace GlobalTheory.Lyndon
theorem _root_.solution (L : List (List A)) :
    (L.map (word K)).prod = ((shuffleList L).map (word K)).sum := by
  induction L with
  | nil => simp [shuffleList, word_nil]
  | cons u L ih =>
    rw [List.map_cons, List.prod_cons, ih, ← Multiset.sum_map_mul_left, shuffleList,
      Multiset.map_bind, Multiset.sum_bind]
    simp only [word_mul_word]
end GlobalTheory.Lyndon
