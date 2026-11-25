-- Prove2me | solution 1 for GlobalTheory.T.neg_one_le_sum_fejer_cos_re_pow_and_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:34.232804+00:00
-- url     : https://prove2.me/submissions/2037b5c7-fc8a-4e04-90ac-29a33b100acb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeightedFejerPositivity
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeightedFejerPositivityStatement
import Theorems.Thm_GlobalTheory_weighted_fejer_positivity


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (J : ℕ) (θ : ℝ), (∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re) ∧ (J : ℝ) / 4 - 3 / 4 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (Complex.exp (θ * I) ^ j).re := by
  first | exact @GlobalTheory.weighted_fejer_positivity | exact GlobalTheory.weighted_fejer_positivity | (intros; apply GlobalTheory.weighted_fejer_positivity <;> assumption)
end _root_.GlobalTheory.T
