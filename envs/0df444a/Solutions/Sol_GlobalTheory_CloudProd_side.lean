-- Prove2me | solution 1 for GlobalTheory.CloudProd.side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:39.344107+00:00
-- url     : https://prove2.me/submissions/f20da338-8782-4056-94ff-50e96abdb796

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SideSucc
import Theorems.Thm_GlobalTheory_CloudProd_side_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CloudProd
namespace GlobalTheory.CloudProd
theorem _root_.solution (c : ℝ) (δ : ℕ → ℝ) (hc : 1 ≤ c) (n : ℕ)
    (h : ∀ j : ℕ, j < n → 2 * c * (j : ℝ) ≤ δ j) :
    ∏ j ∈ Finset.range n, (1 + (1 + c) / max (δ j) 1) ≤ (2 + c) * ((n : ℝ) + 1) := by
  cases n with
  | zero => simp; linarith
  | succ m =>
    refine (side_succ c δ hc m h).trans ?_
    push_cast
    nlinarith
end GlobalTheory.CloudProd
