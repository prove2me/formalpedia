-- Prove2me | solution 1 for GlobalTheory.ZetaLeft.tendsto_cpow_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:24.091837+00:00
-- url     : https://prove2.me/submissions/a701e294-9de5-4f67-9c97-1eff55d089f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft
namespace GlobalTheory.ZetaLeft
theorem _root_.solution {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have := (tendsto_rpow_neg_atTop (y := -c.re) (by linarith)).comp h1
  refine this.congr fun n => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp
end GlobalTheory.ZetaLeft
