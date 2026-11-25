-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_node
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:37.87605+00:00
-- url     : https://prove2.me/submissions/12326623-be77-4197-86a4-ccb88a1f135d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_cloud
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_cloud

set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
namespace GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
theorem _root_.solution (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (i : Fin (2 * r + 2)) :
    param r k hk v b (nodeIdx r k hk i) = -b i := by
  have : Fin.cast (card_eq r k hk) (nodeIdx r k hk i) = Fin.natAdd (k - 1) i := rfl
  simp only [param, this, Fin.append_right]
end GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
