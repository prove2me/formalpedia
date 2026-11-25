-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_cloud
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:27:30.910291+00:00
-- url     : https://prove2.me/submissions/9aaf1317-4e75-475d-9d00-fa9f7759bddd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
namespace GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
theorem _root_.solution (r k : ℕ) (hk : 1 ≤ k) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) (j : Fin (k - 1)) : param r k hk v b (cloudIdx r k j) = v j := by
  have : Fin.cast (card_eq r k hk) (cloudIdx r k j) = Fin.castAdd (2 * r + 2) j := rfl
  simp only [param, this, Fin.append_left]
end GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
