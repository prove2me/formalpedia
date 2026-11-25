-- Prove2me | solution 1 for GlobalTheory.IsAnalyticGroupChart.analyticAt_chart_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:35:02.835158+00:00
-- url     : https://prove2.me/submissions/2ee81cb6-9124-4d3c-9d7e-0e1b4dcbe5c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_chart_exp_eventuallyEq

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
theorem _root_.solution : AnalyticAt ℂ (fun v => φ (h.exp v)) 0 :=
  h.isLocalCommGroupLaw.analyticAt_logChart_symm.congr h.chart_exp_eventuallyEq.symm
end GlobalTheory.IsAnalyticGroupChart
