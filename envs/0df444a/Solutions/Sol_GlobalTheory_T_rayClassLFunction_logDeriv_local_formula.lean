-- Prove2me | solution 1 for GlobalTheory.T.rayClassLFunction_logDeriv_local_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:01.632256+00:00
-- url     : https://prove2.me/submissions/03203611-dbe6-4874-923c-c905eda0d443

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormula
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Theorems.Thm_GlobalTheory_HkLocal_logDeriv_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (t : ℝ), {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}, (analyticOrderNatAt (𝓕.F χ) w : ℝ)) ≤ C * 𝓕.ell t ∧ ∀ s : ℂ, ‖s - (5 / 4 + t * I)‖ ≤ 1 / 2 → 𝓕.F χ s ≠ 0 → ‖deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ ≤ C * 𝓕.ell t := by
  first | exact @GlobalTheory.HkLocal.logDeriv_local | exact GlobalTheory.HkLocal.logDeriv_local | (intros; apply GlobalTheory.HkLocal.logDeriv_local <;> assumption)
end _root_.GlobalTheory.T
