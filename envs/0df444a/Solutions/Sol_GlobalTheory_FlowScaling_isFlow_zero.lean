-- Prove2me | solution 1 for GlobalTheory.FlowScaling.isFlow_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:25:45.854921+00:00
-- url     : https://prove2.me/submissions/dbaceef9-8fd2-4651-847e-1fcae29a0f81

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe

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
theorem _root_.solution {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) : IsFlow l d D (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun s => by simpa using hD s⟩
end GlobalTheory.FlowScaling
