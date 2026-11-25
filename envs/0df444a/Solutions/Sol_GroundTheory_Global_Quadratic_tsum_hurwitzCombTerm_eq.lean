-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.tsum_hurwitzCombTerm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:05.441036+00:00
-- url     : https://prove2.me/submissions/df9d935c-4d0d-4efd-8c30-e7ae00f71d62

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero
import Theorems.Thm_GroundTheory_Global_Quadratic_differentiable_hurwitzComb
import Theorems.Thm_GroundTheory_Global_Quadratic_hasSum_hurwitzCombTerm
import Theorems.Thm_GroundTheory_Global_Quadratic_differentiableOn_tsum_hurwitzCombTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic
namespace GroundTheory.Global.Quadratic
theorem _root_.solution {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {s : ℂ}
    (hs : s ∈ Metric.ball (1 : ℂ) (3 / 2)) :
    ∑' n, hurwitzCombTerm x n s = hurwitzComb x s := by
  have hU : IsOpen (Metric.ball (1 : ℂ) (3 / 2)) := Metric.isOpen_ball
  have hf : AnalyticOnNhd ℂ (fun s ↦ ∑' n, hurwitzCombTerm x n s) (Metric.ball 1 (3 / 2)) :=
    (differentiableOn_tsum_hurwitzCombTerm hx0 hx1).analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (hurwitzComb x) (Metric.ball 1 (3 / 2)) :=
    (differentiable_hurwitzComb x).differentiableOn.analyticOnNhd hU
  have h2 : (2 : ℂ) ∈ Metric.ball (1 : ℂ) (3 / 2) := by
    rw [Metric.mem_ball, dist_eq_norm, show (2 : ℂ) - 1 = 1 by norm_num, norm_one]
    norm_num
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_ball _ _).isPreconnected h2 ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  exact (hasSum_hurwitzCombTerm hx0.le hx1.le hz).tsum_eq
end GroundTheory.Global.Quadratic
