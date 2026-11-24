-- Prove2me | solution 1 for GlobalTheory.Lyndon.le_of_repr_prod_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:04:52.441245+00:00
-- url     : https://prove2.me/submissions/33fba10a-1791-4b3f-b625-605413e28f32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_le_flatten_of_interleaves
import Theorems.Thm_GlobalTheory_Lyndon_of_mem_shuffleList
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
theorem _root_.solution {L : List (List A)} (hL : IsFactors L) {w : List A}
    (h : (wordBasis K A).repr (L.map (word K)).prod w ≠ 0) :
    w.Perm L.flatten ∧ w ≤ L.flatten := by
  rw [prod_word, repr_sum_word] at h
  have hw : w ∈ shuffleList L := by
    by_contra hw
    exact h (by rw [Multiset.count_eq_zero.2 hw, Nat.cast_zero])
  exact ⟨(of_mem_shuffleList L w hw).1,
    le_flatten_of_interleaves w L hL (of_mem_shuffleList L w hw).2⟩
end GlobalTheory.Lyndon
