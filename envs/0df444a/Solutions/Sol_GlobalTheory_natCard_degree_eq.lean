-- Prove2me | solution 1 for GlobalTheory.natCard_degree_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:22.987848+00:00
-- url     : https://prove2.me/submissions/664c2ec2-20e8-4629-9cec-6e5483f85993

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Theorems.Thm_GlobalTheory_ncard_degree_eq

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
    Nat.card {α : σ →₀ ℕ // α.degree = a} = (a + Fintype.card σ - 1).choose a := by
  have h := ncard_degree_eq σ a
  rw [← Nat.card_coe_set_eq] at h
  exact h
end GlobalTheory
