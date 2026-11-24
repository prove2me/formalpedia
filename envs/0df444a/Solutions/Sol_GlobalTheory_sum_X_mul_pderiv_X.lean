-- Prove2me | solution 1 for GlobalTheory.sum_X_mul_pderiv_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:09.950267+00:00
-- url     : https://prove2.me/submissions/8b525571-5b04-47b8-9658-a09300c6f1b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RowAddGenericRowAddTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
variable {K σ ι : Type*} [Field K] [DecidableEq σ] [Fintype ι]
namespace GlobalTheory
theorem _root_.solution (u w : ι → σ) (s : σ) :
    ∑ k, X (u k) * pderiv (w k) (X s : MvPolynomial σ K) = rowAddTerm K u w s := by
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · simp [h]
  · simp [pderiv_X_of_ne h]
end GlobalTheory
