-- Prove2me | solution 1 for GlobalTheory.IsAnalyticGroupChart.exp_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:32:41.065582+00:00
-- url     : https://prove2.me/submissions/aed9edd7-49ba-410c-9574-4fa32fa519a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_map_exp_nhds_zero
import Theorems.Thm_GlobalTheory_IsAnalyticGroupChart_log_exp

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
theorem _root_.solution : ∀ᶠ a in 𝓝 (0 : A), h.exp (h.log (φ a)) = a := by
  rw [← h.map_exp_nhds_zero, eventually_map]
  filter_upwards [h.log_exp] with v hv
  rw [hv]
end GlobalTheory.IsAnalyticGroupChart
