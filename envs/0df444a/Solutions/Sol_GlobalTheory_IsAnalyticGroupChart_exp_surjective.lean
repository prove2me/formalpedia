-- Prove2me | solution 1 for GlobalTheory.IsAnalyticGroupChart.exp_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:35:04.06614+00:00
-- url     : https://prove2.me/submissions/80c20a4d-6e9e-43c4-86cf-74a8ea912ea5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Theorems.Thm_GlobalTheory_surjective_of_isOpenMap_of_compact_of_divisible

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
theorem _root_.solution [CompactSpace A] (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ a : A, ∃ b : A, n • b = a) :
    Function.Surjective h.exp :=
  surjective_of_isOpenMap_of_compact_of_divisible h.isOpenMap_exp hdiv
end GlobalTheory.IsAnalyticGroupChart
