-- Prove2me | solution 1 for MDPComplexity.CircuitValue.expCost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:51:52.013536+00:00
-- url     : https://prove2.me/submissions/07c17901-7bfb-48e9-a3b6-bbfee28a81ee

import Mathlib
import Definitions.Def_MDPComplexity_CircuitValue_Model
import Definitions.Def_MDPComplexity_CircuitValue_Circuit
import Definitions.Def_MDPComplexity_CircuitValue_Reduction
set_option autoImplicit false
open MDPComplexity.CircuitValue

theorem solution {k : ℕ} [NeZero k] (C : Circuit k) (δ : C.toMDP.Policy) :
    0 ≤ C.toMDP.expCost (some (Circuit.lastIdx k)) δ k := by
  unfold MDP.expCost
  refine Finset.sum_nonneg (fun x _ => mul_nonneg ?_ ?_)
  · unfold MDP.trajProb
    refine mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg (fun t _ => ?_))
    exact C.toMDP.p_nonneg _ _ _ _
  · unfold MDP.trajCost
    refine Finset.sum_nonneg (fun t _ => ?_)
    show 0 ≤ C.cost (x t)
    cases x t with
    | none => simp [Circuit.cost]
    | some i => simp only [Circuit.cost]; split_ifs <;> norm_num
