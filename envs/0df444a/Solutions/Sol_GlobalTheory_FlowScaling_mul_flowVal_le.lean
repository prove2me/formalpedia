-- Prove2me | solution 1 for GlobalTheory.FlowScaling.mul_flowVal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:27:38.90493+00:00
-- url     : https://prove2.me/submissions/a37299da-5925-4d21-82d6-882bead2f8f4

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
theorem _root_.solution (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    (l : ℝ) * flowVal d x ≤ ∑ a, D a := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  unfold flowVal
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have h2 := hx.2 a
  have h3 : 0 ≤ ∑ i ∈ oddLevels d, x (a - (i : ZMod d)) i :=
    Finset.sum_nonneg fun i _ => hx.1 _ i
  have h4 : (l : ℝ) * ∑ i ∈ oddLevels d, x a i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact absurd (Finset.mem_filter.1 hi).2 (by decide)
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi0) (hx.1 a i)
  linarith
end GlobalTheory.FlowScaling
