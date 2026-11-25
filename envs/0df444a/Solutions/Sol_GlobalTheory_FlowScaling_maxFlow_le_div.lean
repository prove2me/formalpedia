-- Prove2me | solution 1 for GlobalTheory.FlowScaling.maxFlow_le_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:42:02.892433+00:00
-- url     : https://prove2.me/submissions/c8dbe543-b00e-4d17-b3e7-16c20c48ce83

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
import Theorems.Thm_GlobalTheory_FlowScaling_flowVal_le
import Theorems.Thm_GlobalTheory_FlowScaling_maxFlow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.FlowScaling
variable {l d : ℕ} [NeZero d]
namespace GlobalTheory.FlowScaling
theorem _root_.solution (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    maxFlow l d D ≤ (∑ a, D a) / l :=
  maxFlow_le hD fun _ hx => flowVal_le hl hx
end GlobalTheory.FlowScaling
