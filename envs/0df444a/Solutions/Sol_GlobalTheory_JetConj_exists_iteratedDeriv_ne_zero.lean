-- Prove2me | solution 1 for GlobalTheory.JetConj.exists_iteratedDeriv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:23:26.738824+00:00
-- url     : https://prove2.me/submissions/97ab91b0-4e8c-4e6a-8369-3ed5256daa0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.JetConj
variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}
namespace GlobalTheory.JetConj
theorem _root_.solution (hg : AnalyticAt ℂ g 0) (h0 : ¬ g =ᶠ[𝓝 0] 0) :
    ∃ k, iteratedDeriv k g 0 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hg.eventually_analyticAt
  have hd : DifferentiableOn ℂ g (Metric.ball 0 ε) := fun y hy =>
    (hball y hy).differentiableAt.differentiableWithinAt
  filter_upwards [Metric.ball_mem_nhds 0 hε] with z hz
  have hs := Complex.hasSum_taylorSeries_on_ball hd hz
  simp only [hcon, smul_zero] at hs
  exact (hasSum_zero.unique hs).symm
end GlobalTheory.JetConj
