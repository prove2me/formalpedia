-- Prove2me | solution 1 for GlobalTheory.FlowScaling.maxFlow_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:50:10.30004+00:00
-- url     : https://prove2.me/submissions/3b919bf3-929b-436a-83e2-7c07249054d0

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
import Theorems.Thm_GlobalTheory_FlowScaling_isFlow_zero
import Theorems.Thm_GlobalTheory_FlowScaling_le_maxFlow

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
    0 ≤ maxFlow l d D := by
  have := le_maxFlow hl (isFlow_zero (l := l) hD)
  simpa [flowVal] using this
end GlobalTheory.FlowScaling
