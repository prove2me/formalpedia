-- Prove2me | solution 1 for GlobalTheory.ShufflePositions.count_bind_shuffle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:15:03.304834+00:00
-- url     : https://prove2.me/submissions/f8cec87d-7e49-46fc-80cb-b8264f0d03b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CountBindWordShuffleByPositions
import Theorems.Thm_GlobalTheory_ShufflePositions_count_single
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory
namespace GlobalTheory
namespace ShufflePositions
variable {A : Type} [DecidableEq A]
private theorem sum_map_count_singleton (X : List A) (s : Multiset (List A)) :
    (s.map fun v => ({v} : Multiset (List A)).count X).sum = s.count X := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons, Multiset.count_singleton,
      add_comm]
end ShufflePositions
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open GlobalTheory
open GlobalTheory.ShufflePositions
variable {A : Type} [DecidableEq A]
namespace GlobalTheory.ShufflePositions
theorem _root_.solution (A : Type) [DecidableEq A] (n : ℕ) (w : Fin n → A)
    (s₁ s₂ : Multiset (List A)) :
    (s₁.bind fun u => s₂.bind fun v => Shuffle.shuffle u v).count (List.ofFn w) =
      ∑ ε : Fin n → Bool, s₁.count (((List.finRange n).filter fun j => !ε j).map w) *
        s₂.count (((List.finRange n).filter ε).map w) := by
  simp only [Multiset.count_bind, count_single n w, Multiset.sum_map_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [Multiset.sum_map_mul_left, Multiset.sum_map_mul_right, sum_map_count_singleton]
end GlobalTheory.ShufflePositions
