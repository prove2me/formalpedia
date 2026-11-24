-- Prove2me | solution 1 for GlobalTheory.T.mobius_change_of_variables
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:18:28.385683+00:00
-- url     : https://prove2.me/submissions/cb5fb2e1-859e-4a9e-8402-0a2660dd2882

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusChangeOfVariables
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusChangeOfVariablesStatement
import Theorems.Thm_GlobalTheory_FibLine_MoebiusLintegral_lintegral_moebius


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
theorem _root_.solution : ∀ (β c : ℂ), c ≠ 0 → ∀ H : ℂ → ℝ≥0∞, Measurable H →
    ∫⁻ x : ℂ, ENNReal.ofReal (‖c / (1 + β * x) ^ 2‖ ^ 2) * H (c * x / (1 + β * x)) = ∫⁻ y : ℂ, H y := by
  first | exact @GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius | exact GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius | (intros; apply GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius <;> assumption)
end _root_.GlobalTheory.T
