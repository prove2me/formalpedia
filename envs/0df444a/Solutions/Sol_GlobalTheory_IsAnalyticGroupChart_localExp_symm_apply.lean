-- Prove2me | solution 1 for GlobalTheory.IsAnalyticGroupChart.localExp_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:55:32.445602+00:00
-- url     : https://prove2.me/submissions/68ff0a3e-48f9-4301-bf63-7ceb2819d0f7

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
theorem _root_.solution (a : A) : h.localExp.symm a = h.log (φ a) := rfl
end GlobalTheory.IsAnalyticGroupChart
