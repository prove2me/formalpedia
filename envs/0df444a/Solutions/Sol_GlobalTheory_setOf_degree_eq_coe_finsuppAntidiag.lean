-- Prove2me | solution 1 for GlobalTheory.setOf_degree_eq_coe_finsuppAntidiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:32:45.149801+00:00
-- url     : https://prove2.me/submissions/25e8e65f-8bc0-45c4-a425-7b667ca56bdc

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
theorem _root_.solution (σ : Type*) [Fintype σ] [DecidableEq σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a} = ↑(finsuppAntidiag (univ : Finset σ) a) := by
  ext α
  simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
end GlobalTheory
