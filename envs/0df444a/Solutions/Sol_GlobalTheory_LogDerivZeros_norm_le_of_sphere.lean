-- Prove2me | solution 1 for GlobalTheory.LogDerivZeros.norm_le_of_sphere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:50:14.88978+00:00
-- url     : https://prove2.me/submissions/66d5baf8-cdce-4a05-be2d-b07f128b7f48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsFactorOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LogDerivZeros
namespace GlobalTheory.LogDerivZeros
theorem _root_.solution {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (Metric.closedBall 0 1)) {B : ℝ}
    (hb : ∀ z : ℂ, ‖z‖ = 1 → ‖g z‖ ≤ B) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖g z‖ ≤ B := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball 0 1)
    Metric.isBounded_ball (hg.differentiableOn.diffContOnCl_ball subset_rfl) ?_ ?_
  · intro u hu
    rw [frontier_ball _ one_ne_zero] at hu
    exact hb u (by simpa using hu)
  · rw [closure_ball _ one_ne_zero]; simpa using hz
end GlobalTheory.LogDerivZeros
