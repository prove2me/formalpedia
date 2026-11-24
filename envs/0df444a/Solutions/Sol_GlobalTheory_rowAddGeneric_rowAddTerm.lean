-- Prove2me | solution 1 for GlobalTheory.rowAddGeneric_rowAddTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:39.090285+00:00
-- url     : https://prove2.me/submissions/cd6cb895-f4eb-4d29-b1db-5274c5577876

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
theorem _root_.solution (u w : ι → σ) (huw : ∀ k l, u k ≠ w l) (s : σ) :
    rowAddGeneric u w (rowAddTerm K u w s) = Polynomial.C (rowAddTerm K u w s) := by
  have h0 : ∀ k, rowAddTerm K u w (u k) = 0 := fun k => by
    simp [rowAddTerm, huw k]
  conv_lhs => rw [rowAddTerm]
  conv_rhs => rw [rowAddTerm]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · simp [rowAddGeneric, h0]
  · simp
end GlobalTheory
