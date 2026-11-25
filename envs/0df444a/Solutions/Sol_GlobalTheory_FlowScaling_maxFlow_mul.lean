-- Prove2me | solution 1 for GlobalTheory.FlowScaling.maxFlow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:16:39.301025+00:00
-- url     : https://prove2.me/submissions/a64ba95f-9d77-42c6-98f5-e14889330bb6

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
import Theorems.Thm_GlobalTheory_FlowScaling_maxFlow_le_div
import Theorems.Thm_GlobalTheory_FlowScaling_mul_maxFlow_le

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
theorem _root_.solution (hl : 1 ≤ l) {c : ℝ} {D : ZMod d → ℝ} (hc : 0 ≤ c) (hD : ∀ a, 0 ≤ D a) :
    maxFlow l d (fun a => c * D a) = c * maxFlow l d D := by
  refine le_antisymm ?_ (mul_maxFlow_le hl hc hD fun _ => le_rfl)
  rcases hc.eq_or_lt with rfl | hc0
  · have := maxFlow_le_div (D := fun a => 0 * D a) hl (fun a => by simp)
    simpa using this
  · have := mul_maxFlow_le (c := c⁻¹) (D := fun a => c * D a) (D' := D) hl (inv_nonneg.2 hc)
      (fun a => mul_nonneg hc (hD a)) (fun a => by rw [inv_mul_cancel_left₀ hc0.ne'])
    rwa [inv_mul_le_iff₀ hc0] at this
end GlobalTheory.FlowScaling
