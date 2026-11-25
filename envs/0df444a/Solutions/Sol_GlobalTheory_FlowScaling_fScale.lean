-- Prove2me | solution 1 for GlobalTheory.FlowScaling.fScale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:22:40.919991+00:00
-- url     : https://prove2.me/submissions/f0d0cb9b-4019-46aa-9ae8-57a03454446c

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
import Theorems.Thm_GlobalTheory_FlowScaling_maxFlow_mul

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
theorem _root_.solution : FScale := by
  intro l d _ hl c D hc hD
  unfold Fnum
  rw [maxFlow_mul (by omega) hc hD, ← Finset.mul_sum]
  ring
end GlobalTheory.FlowScaling
