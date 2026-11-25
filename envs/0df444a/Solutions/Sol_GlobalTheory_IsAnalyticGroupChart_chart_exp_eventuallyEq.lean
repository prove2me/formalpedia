-- Prove2me | solution 1 for GlobalTheory.IsAnalyticGroupChart.chart_exp_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:23:23.621719+00:00
-- url     : https://prove2.me/submissions/ac2e9ac8-6f9f-427a-b36a-6cddaaa86303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq

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
variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [AddCommGroup A]
  [TopologicalSpace A]
open GlobalTheory.IsAnalyticGroupChart
variable {φ : OpenPartialHomeomorph A V} (h : IsAnalyticGroupChart φ)
include h
variable [IsTopologicalAddGroup A]
variable [FiniteDimensional ℂ V] [CompleteSpace V]
namespace GlobalTheory.IsAnalyticGroupChart
theorem _root_.solution :
    (fun v => φ (h.exp v)) =ᶠ[𝓝 0] h.isLocalCommGroupLaw.logChart.symm := by
  have t0 : Tendsto h.isLocalCommGroupLaw.logChart.symm (𝓝 0) (𝓝 0) := by
    simpa [ContinuousAt] using h.isLocalCommGroupLaw.analyticAt_logChart_symm.continuousAt
  filter_upwards [h.exp_eventuallyEq,
    t0.eventually (φ.eventually_right_inverse h.zero_mem_target)] with v h1 h2
  rw [h1, localExp_apply, h2]
end GlobalTheory.IsAnalyticGroupChart
