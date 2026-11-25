-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_node
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:40:47.135506+00:00
-- url     : https://prove2.me/submissions/40064960-05ce-448c-85a6-9b0eebffa204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_cloud
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_node
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_sign_cloud
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_cloud
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_node
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_cloud

set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
namespace GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
theorem _root_.solution (r k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + 2)) :
    sign r k hk (nodeIdx r k hk i) = decide (Even i.val) := by
  have : Fin.cast (card_eq r k hk) (nodeIdx r k hk i) = Fin.natAdd (k - 1) i := rfl
  simp only [sign, this, Fin.append_right]
end GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
