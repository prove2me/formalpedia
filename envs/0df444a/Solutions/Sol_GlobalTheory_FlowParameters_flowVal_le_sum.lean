-- Prove2me | solution 1 for GlobalTheory.FlowParameters.flowVal_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:33:27.910161+00:00
-- url     : https://prove2.me/submissions/4daea294-a74a-46bb-bc81-e95c6d07b34a

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ParametersSmallBound
import Theorems.Thm_GlobalTheory_FlowParameters_sum_inflow

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
    (hx : IsFlow l d D x) : flowVal d x ≤ ∑ a, D a := by
  unfold flowVal
  rw [← sum_inflow]
  refine Finset.sum_le_sum fun a _ => ?_
  have h1 := hx.2 a
  have h2 : 0 ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hx.1 a i)
  linarith
end GlobalTheory.FlowParameters
