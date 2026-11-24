-- Prove2me | solution 1 for GlobalTheory.natCard_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:36.037802+00:00
-- url     : https://prove2.me/submissions/d673c136-b7f9-4574-aa70-f35f89812f77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Theorems.Thm_GlobalTheory_ncard_degree_le

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
    Nat.card {α : σ →₀ ℕ // α.degree ≤ k} = (k + Fintype.card σ).choose (Fintype.card σ) := by
  have h := ncard_degree_le σ k
  rw [← Nat.card_coe_set_eq] at h
  exact h
end GlobalTheory
