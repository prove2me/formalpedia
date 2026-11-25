-- Prove2me | solution 1 for GlobalTheory.FlowScaling.maxFlow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:33:28.413802+00:00
-- url     : https://prove2.me/submissions/7577a519-3ff7-4705-84a2-6086d1bb4f2f

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
import Theorems.Thm_GlobalTheory_FlowScaling_isFlow_zero

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
theorem _root_.solution {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) {B : ℝ}
    (h : ∀ x, IsFlow l d D x → flowVal d x ≤ B) : maxFlow l d D ≤ B := by
  refine csSup_le ⟨_, _, isFlow_zero hD, rfl⟩ ?_
  rintro t ⟨y, hy, rfl⟩
  exact h y hy
end GlobalTheory.FlowScaling
