-- Prove2me | solution 1 for GlobalTheory.three_mul_div_four_le_log_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:58.131273+00:00
-- url     : https://prove2.me/submissions/e6c82e8f-5dba-4fa2-8ae8-60e7667eaded

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpQuadraticLowerAndLogLinearLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 3) :
    3 * u / 4 ≤ Real.log (1 + u) := by
  have hp : 0 < 1 + u := by linarith
  refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hp)
  have : (1 + u)⁻¹ ≤ 1 - 3 * u / 4 := by
    rw [inv_eq_one_div, div_le_iff₀ hp]
    nlinarith
  linarith
end GlobalTheory
