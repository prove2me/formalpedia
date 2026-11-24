-- Prove2me | solution 1 for GlobalTheory.LGrowth.norm_LFunction_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:27:11.578868+00:00
-- url     : https://prove2.me/submissions/843d94ff-2c43-42d7-ba11-22b80fd54cd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtMellinSummatory
import Theorems.Thm_GlobalTheory_LGrowth_norm_partialSum_le
import Theorems.Thm_GlobalTheory_LGrowth_norm_mellin_summatory_le
import Theorems.Thm_GlobalTheory_LGrowth_LFunction_eq_mul_mellin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LGrowth
open Filter Topology Asymptotics
namespace GlobalTheory.LGrowth
theorem _root_.solution : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ s : ℂ, 0 < s.re → ‖LFunction χ s‖ ≤ q * ‖s‖ / s.re := by
  intro q _ χ hχ s hs
  rw [LFunction_eq_mul_mellin q χ hχ hs, norm_mul]
  refine (mul_le_mul_of_nonneg_left
    (norm_mellin_summatory_le (norm_partialSum_le q χ hχ) hs) (norm_nonneg s)).trans ?_
  exact le_of_eq (by ring)
end GlobalTheory.LGrowth
