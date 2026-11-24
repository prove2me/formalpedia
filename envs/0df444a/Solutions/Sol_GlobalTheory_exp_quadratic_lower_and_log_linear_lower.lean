-- Prove2me | solution 1 for GlobalTheory.exp_quadratic_lower_and_log_linear_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:31.248119+00:00
-- url     : https://prove2.me/submissions/518815da-b62d-4d67-9d79-4ec71f9c7185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpQuadraticLowerAndLogLinearLower
import Theorems.Thm_GlobalTheory_one_add_add_sq_div_three_le_exp
import Theorems.Thm_GlobalTheory_three_mul_div_four_le_log_one_add

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
theorem _root_.solution :
    (∀ u : ℝ, |u| ≤ 1 → 1 + u + u ^ 2 / 3 ≤ Real.exp u) ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 3 → 3 * u / 4 ≤ Real.log (1 + u) :=
  ⟨one_add_add_sq_div_three_le_exp, three_mul_div_four_le_log_one_add⟩
end GlobalTheory
