-- Prove2me | solution 1 for GlobalTheory.IsAnalyticGroupChart.eq_exp_of_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:56:22.795795+00:00
-- url     : https://prove2.me/submissions/f0e83cba-5bb3-48c3-99da-57b2cb372bba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_map_exp_nhds_zero
import Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_log_exp
import Theorems.Thm_GlobalTheory_addMonoidHom_eq_of_eventuallyEq


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
theorem _root_.solution {e : V →+ A} (he : ∀ᶠ a in 𝓝 (0 : A), e (h.log (φ a)) = a) :
    e = h.exp := by
  refine addMonoidHom_eq_of_eventuallyEq ?_
  filter_upwards [Tendsto.eventually h.map_exp_nhds_zero.le he, h.log_exp] with v h1 h2
  rwa [h2] at h1
end GlobalTheory.IsAnalyticGroupChart
