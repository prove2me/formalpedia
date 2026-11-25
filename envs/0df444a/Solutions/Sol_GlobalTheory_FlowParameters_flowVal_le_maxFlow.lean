-- Prove2me | solution 1 for GlobalTheory.FlowParameters.flowVal_le_maxFlow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:01.51081+00:00
-- url     : https://prove2.me/submissions/86d38c07-3079-4b8a-b80e-ee397525503e

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ParametersSmallBound
import Theorems.Thm_GlobalTheory_FlowParameters_flowVal_le_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.FlowParameters
namespace GlobalTheory.FlowParameters
theorem _root_.solution (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (hx : IsFlow l d D x) : flowVal d x ≤ maxFlow l d D := by
  refine le_csSup ⟨∑ a, D a, ?_⟩ ⟨x, hx, rfl⟩
  rintro t ⟨z, hz, rfl⟩
  exact flowVal_le_sum l d D z hz
end GlobalTheory.FlowParameters
