-- Prove2me | solution 1 for GlobalTheory.analyticAt_doublingLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:08.340171+00:00
-- url     : https://prove2.me/submissions/0aaab554-7573-40c5-ad5a-2282fd61cbf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Theorems.Thm_GlobalTheory_iterate_mem_ball_of_contraction
import Theorems.Thm_GlobalTheory_tendstoUniformlyOn_doublingLog_of_contraction
import Theorems.Thm_GlobalTheory_exists_ball_contraction
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_of_tendstoLocallyUniformlyOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {ε : V → V} {r C : ℝ}
variable [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution [FiniteDimensional ℂ V] (ha : AnalyticAt ℂ ε 0)
    (h : (fun x => ε x - (2 : ℂ)⁻¹ • x) =O[𝓝 0] fun x => ‖x‖ ^ 2) :
    AnalyticAt ℂ (doublingLog ε) 0 := by
  obtain ⟨r, hr, C, hC0, hc, hC⟩ := exists_ball_contraction h
  obtain ⟨s, hs, hsa⟩ := Metric.eventually_nhds_iff_ball.mp ha.eventually_analyticAt
  have h1 : ball (0 : V) (min r s) ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  have h2 : ball (0 : V) (min r s) ⊆ ball 0 s := ball_subset_ball (min_le_right _ _)
  have hc' : ∀ x ∈ ball (0 : V) (min r s), ‖ε x‖ ≤ 5 / 8 * ‖x‖ := fun x hx => hc x (h1 hx)
  have hd : ∀ j : ℕ, DifferentiableOn ℂ ε^[j] (ball 0 (min r s)) := fun j =>
    DifferentiableOn.iterate (fun x hx => (hsa x (h2 hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => iterate_mem_ball_of_contraction hc' hx 1) j
  refine SCV.analyticAt_of_differentiableOn
    (SCV.differentiableOn_of_tendstoLocallyUniformlyOn isOpen_ball
      ((tendstoUniformlyOn_doublingLog_of_contraction hc hC0 hC).mono
        h1).tendstoLocallyUniformlyOn
      (Eventually.of_forall fun j => (hd j).const_smul _)) (ball_mem_nhds 0 (lt_min hr hs))
end GlobalTheory
