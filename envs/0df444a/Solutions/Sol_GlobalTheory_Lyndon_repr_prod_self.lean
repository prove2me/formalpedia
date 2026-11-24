-- Prove2me | solution 1 for GlobalTheory.Lyndon.repr_prod_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:14:50.806936+00:00
-- url     : https://prove2.me/submissions/dec4ddaf-57df-4811-8afd-4ecae08bbbdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_flatten_mem_shuffleList
import Theorems.Thm_GlobalTheory_Lyndon_prod_word
import Theorems.Thm_GlobalTheory_Lyndon_repr_sum_word

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
namespace GlobalTheory.Lyndon
theorem _root_.solution [CharZero K] (L : List (List A)) :
    (wordBasis K A).repr (L.map (word K)).prod L.flatten ≠ 0 := by
  rw [prod_word, repr_sum_word, Nat.cast_ne_zero]
  exact Multiset.count_ne_zero.2 (flatten_mem_shuffleList L)
end GlobalTheory.Lyndon
