-- Prove2me | solution 1 for GlobalTheory.Lin.Repulsion.pole_far
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:43:56.238866+00:00
-- url     : https://prove2.me/submissions/72f63eb2-7e64-4f0c-b4b7-7866e87d56e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.Repulsion
namespace GlobalTheory.Lin.Repulsion
theorem _root_.solution {β t : ℝ} (hβ : β < 1) (hβ' : 1 / 2 ≤ β) (h : ¬ ‖(β : ℂ) - (2 + t * I)‖ ≤ 3) (j : ℕ) :
    ‖1 / ((2 : ℂ) + t * I - 1) ^ j‖ ≤ 1 / 2 ^ j := by
  have h1 : 2 ≤ ‖(2 : ℂ) + t * I - 1‖ := by
    have e : (β : ℂ) - (2 + t * I) = -((2 : ℂ) + t * I - 1) + ((β - 1 : ℝ) : ℂ) := by push_cast; ring
    have := norm_add_le (-((2 : ℂ) + t * I - 1)) ((β - 1 : ℝ) : ℂ)
    rw [← e, norm_neg, Complex.norm_real, Real.norm_of_nonpos (by linarith)] at this
    linarith
  rw [norm_div, norm_one, norm_pow]
  gcongr
end GlobalTheory.Lin.Repulsion
