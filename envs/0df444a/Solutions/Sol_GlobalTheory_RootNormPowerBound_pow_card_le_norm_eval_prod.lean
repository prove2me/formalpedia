-- Prove2me | solution 1 for GlobalTheory.RootNormPowerBound.pow_card_le_norm_eval_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:18.053408+00:00
-- url     : https://prove2.me/submissions/310c53a0-0e3c-40bf-81c5-703040339e6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRootNormSubPowLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.RootNormPowerBound
open Polynomial
namespace GlobalTheory.RootNormPowerBound
theorem _root_.solution {K : Type u_1} [NormedField K] (x : K) (c : ℝ) (hc : 0 ≤ c)
    (s : Multiset K) (hs : ∀ a ∈ s, c ≤ ‖a - x‖) :
    c ^ Multiset.card s ≤ ‖Polynomial.eval x (s.map fun a => X - C a).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons, eval_mul, norm_mul, mul_comm]
    have ha : c ≤ ‖eval x (X - C a)‖ := by
      rw [eval_sub, eval_X, eval_C, norm_sub_rev]
      exact hs a (Multiset.mem_cons_self a s)
    exact mul_le_mul ha (ih fun t ht => hs t (Multiset.mem_cons_of_mem ht)) (pow_nonneg hc _)
      (norm_nonneg _)
end GlobalTheory.RootNormPowerBound
