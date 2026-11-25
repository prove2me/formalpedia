-- Prove2me | solution 1 for GlobalTheory.IsAnalyticGroupChart.log_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:55:37.443997+00:00
-- url     : https://prove2.me/submissions/b18735cc-311d-4f75-89d6-b2de840de0fa

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
omit [FiniteDimensional ℂ V]
namespace GlobalTheory.IsAnalyticGroupChart
theorem _root_.solution :
    ∀ᶠ p in 𝓝 (0 : A × A), h.log (φ (p.1 + p.2)) = h.log (φ p.1) + h.log (φ p.2) := by
  have t1 : Tendsto (fun p : A × A => p.1) (𝓝 0) (𝓝 0) := continuous_fst.tendsto 0
  have t2 : Tendsto (fun p : A × A => p.2) (𝓝 0) (𝓝 0) := continuous_snd.tendsto 0
  have hl := φ.eventually_left_inverse h.zero_mem_source
  filter_upwards [((h.tendsto.comp t1).prodMk_nhds (h.tendsto.comp t2)).eventually
    h.isLocalCommGroupLaw.log_law, t1.eventually hl, t2.eventually hl] with p h1 h2 h3
  simpa [chartLaw, h2, h3] using h1
end GlobalTheory.IsAnalyticGroupChart
