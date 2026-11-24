-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.norm_indicator_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:32:17.168176+00:00
-- url     : https://prove2.me/submissions/56801c0b-1d45-4820-9d03-0ca4123db5a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth

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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable {E : ℝ → ℂ} {C : ℝ}
namespace GlobalTheory.Hk.RayCont
theorem _root_.solution (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x) (x : ℝ) :
    ‖(Set.Ioi (1 : ℝ)).indicator E x‖ ≤ ‖C * Real.sqrt x‖ := by
  by_cases hx : x ∈ Set.Ioi (1 : ℝ)
  · rw [Set.indicator_of_mem hx]
    exact (hC x (le_of_lt hx)).trans (Real.le_norm_self _)
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact norm_nonneg _
end GlobalTheory.Hk.RayCont
