-- Prove2me | solution 1 for GlobalTheory.FlowScaling.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:43:45.077177+00:00
-- url     : https://prove2.me/submissions/f9ea6693-5474-4409-b09c-a4fb4419d932

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
import Theorems.Thm_GlobalTheory_FlowScaling_fScale
import Theorems.Thm_GlobalTheory_FlowScaling_thetaShift
import Theorems.Thm_GlobalTheory_FlowScaling_thetaConst

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
theorem _root_.solution : FScale ∧ ThetaShift ∧ ThetaConst := ⟨fScale, thetaShift, thetaConst⟩
end GlobalTheory.FlowScaling
