-- Prove2me | solution 1 for GlobalTheory.ncard_degree_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:46.569446+00:00
-- url     : https://prove2.me/submissions/f26698ac-7a10-4c98-bf37-8d95e87a04df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Theorems.Thm_GlobalTheory_setOf_degree_eq_coe_finsuppAntidiag

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
theorem _root_.solution (σ : Type*) [Fintype σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a}.ncard = (a + Fintype.card σ - 1).choose a := by
  classical
  rw [setOf_degree_eq_coe_finsuppAntidiag, Set.ncard_coe_finset,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Nat.add_comm]
end GlobalTheory
