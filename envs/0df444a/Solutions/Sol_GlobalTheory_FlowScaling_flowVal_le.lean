-- Prove2me | solution 1 for GlobalTheory.FlowScaling.flowVal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:34:19.350829+00:00
-- url     : https://prove2.me/submissions/3f582626-4916-491b-8dfb-634294263687

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
import Theorems.Thm_GlobalTheory_FlowScaling_mul_flowVal_le

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
theorem _root_.solution (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ (∑ a, D a) / l := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  rw [le_div_iff₀ hl0, mul_comm]
  exact mul_flowVal_le hl hx
end GlobalTheory.FlowScaling
