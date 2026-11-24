-- Prove2me | solution 1 for GlobalTheory.fintypeCard_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:55.508611+00:00
-- url     : https://prove2.me/submissions/e2364c51-17ee-4688-92bb-93f95389fdf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Theorems.Thm_GlobalTheory_natCard_degree_le

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
theorem _root_.solution (σ : Type*) [Fintype σ] (k : ℕ)
    [Fintype {α : σ →₀ ℕ // α.degree ≤ k}] :
    Fintype.card {α : σ →₀ ℕ // α.degree ≤ k} =
      (k + Fintype.card σ).choose (Fintype.card σ) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_degree_le σ k
end GlobalTheory
