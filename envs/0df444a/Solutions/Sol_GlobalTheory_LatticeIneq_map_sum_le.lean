-- Prove2me | solution 1 for GlobalTheory.LatticeIneq.map_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:41:31.158957+00:00
-- url     : https://prove2.me/submissions/6ca38d1b-56f4-4f76-83f3-3bb0aa4d0d79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsReducedCombination
import Theorems.Thm_GlobalTheory_LatticeIneq_weighted_add_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open GlobalTheory.LatticeIneq
variable {X : Type} [AddCommGroup X]
namespace GlobalTheory.LatticeIneq
theorem _root_.solution (q : QuadraticMap ℤ X ℝ) (hq : ∀ x, 0 ≤ q x) {I : Type} (s : Finset I)
    (v : I → X) : q (∑ x ∈ s, v x) ≤ s.card * ∑ x ∈ s, q (v x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · have hpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
      have h := weighted_add_le q hq s.card (∑ x ∈ s, v x) (v i)
      rw [add_comm (v i)]
      push_cast
      refine le_of_mul_le_mul_left ?_ hpos
      have h2 := mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℝ) ≤ (s.card : ℝ) + 1)
      nlinarith
end GlobalTheory.LatticeIneq
