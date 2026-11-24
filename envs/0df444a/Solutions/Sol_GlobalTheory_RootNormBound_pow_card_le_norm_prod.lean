-- Prove2me | solution 1 for GlobalTheory.RootNormBound.pow_card_le_norm_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:16.389469+00:00
-- url     : https://prove2.me/submissions/04fc73ad-a2fc-460a-b471-64b45b04ab8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowCardLeNormProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RootNormBound
open Polynomial
namespace GlobalTheory.RootNormBound
theorem _root_.solution {ε : ℝ} (hε : 0 ≤ ε) (s : Multiset ℂ)
    (hs : ∀ t ∈ s, ε ≤ ‖t‖) :
    ε ^ Multiset.card s ≤ ‖(s.map (fun a => (0 : ℂ) - a)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, norm_mul, mul_comm]
    have ha : ε ≤ ‖(0 : ℂ) - a‖ := by
      rw [zero_sub, norm_neg]
      exact hs a (Multiset.mem_cons_self a s)
    exact mul_le_mul ha (ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)) (pow_nonneg hε _)
      (norm_nonneg _)
end GlobalTheory.RootNormBound
