-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_cloud
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:51:09.002524+00:00
-- url     : https://prove2.me/submissions/aca6a2bd-eb82-4a47-bc3e-e25e192f3f78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_cloud
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_node
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_cloud
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_node

set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
namespace GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
theorem _root_.solution (r k : ℕ) (hk : 1 ≤ k) (j : Fin (k - 1)) :
    sign r k hk (cloudIdx r k j) = true := by
  have : Fin.cast (card_eq r k hk) (cloudIdx r k j) = Fin.castAdd (2 * r + 2) j := rfl
  simp only [sign, this, Fin.append_left]
end GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps
