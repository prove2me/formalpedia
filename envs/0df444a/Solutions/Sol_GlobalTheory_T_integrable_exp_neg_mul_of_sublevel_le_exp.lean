-- Prove2me | solution 1 for GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:14:28.75724+00:00
-- url     : https://prove2.me/submissions/12028ed8-681c-4ef9-b235-9019d92fa82a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegrableExpNegMulOfSublevelGrowth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegrableExpNegMulOfSublevelGrowthStatement
import Theorems.Thm_GlobalTheory_integrable_exp_neg_mul_of_sublevel_growth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (d : X → ℝ) (a b C : ℝ), Measurable d → (∀ x, 0 ≤ d x) → (∀ r : ℝ, 0 ≤ r → μ {x | d x ≤ r} ≤ ENNReal.ofReal (C * Real.exp (a * r))) → a < b → Integrable (fun x => Real.exp (-(b * d x))) μ := by
  first | exact @GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth | exact GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth | (intros; apply GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth <;> assumption)
end _root_.GlobalTheory.T
