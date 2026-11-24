-- Prove2me | solution 1 for GlobalTheory.T.stereographic_measure_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:27.519363+00:00
-- url     : https://prove2.me/submissions/e0cf64bd-8834-486f-9209-eae542060635

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChange
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChangeStatement
import Theorems.Thm_GlobalTheory_FibLine_lintegral_comp_fsDens


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ g : ℝ → ℝ≥0∞, Measurable g →
    ∫⁻ x : ℂ, g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) =
      ∫⁻ t in Set.Ioo (0:ℝ) 1, g t := by
  first | exact @GlobalTheory.FibLine.lintegral_comp_fsDens | exact GlobalTheory.FibLine.lintegral_comp_fsDens | (intros; apply GlobalTheory.FibLine.lintegral_comp_fsDens <;> assumption)
end _root_.GlobalTheory.T
