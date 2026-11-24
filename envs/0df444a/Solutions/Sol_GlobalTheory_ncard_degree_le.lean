-- Prove2me | solution 1 for GlobalTheory.ncard_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:57.344394+00:00
-- url     : https://prove2.me/submissions/48032d09-e584-4d19-96f8-59533bd56496

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
namespace GlobalTheory
theorem _root_.solution (σ : Type*) [Fintype σ] (k : ℕ) :
    {α : σ →₀ ℕ | α.degree ≤ k}.ncard = (k + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  have hset : {α : σ →₀ ℕ | α.degree ≤ k} =
      ↑((range (k + 1)).biUnion fun a => finsuppAntidiag (univ : Finset σ) a) := by
    ext α
    simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion]
  · simp_rw [Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, ← Nat.multichoose_eq]
    exact Nat.sum_range_multichoose k _
  · intro a _ b _ hab
    exact Finset.disjoint_left.2 fun α h1 h2 =>
      hab ((Finset.mem_finsuppAntidiag.1 h1).1.symm.trans (Finset.mem_finsuppAntidiag.1 h2).1)
end GlobalTheory
