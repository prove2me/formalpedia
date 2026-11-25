-- Prove2me | solution 1 for GlobalTheory.FlowScaling.thetaConst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:27:40.315312+00:00
-- url     : https://prove2.me/submissions/3af4db5c-6898-4be0-9ceb-53ed6cdd20cb

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
theorem _root_.solution : ThetaConst := by
  intro n m D T hm hD hT h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_iff₀ hm'] at h
  have e : 6 * ((D + 4) / T) * n = 6 * (D + 4) * n / T := by ring
  rw [e, div_le_iff₀ hT]
  nlinarith [mul_nonneg hn (sub_nonneg.2 hD)]
end GlobalTheory.FlowScaling
