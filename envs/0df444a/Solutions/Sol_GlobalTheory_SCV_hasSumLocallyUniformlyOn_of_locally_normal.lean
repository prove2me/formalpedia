-- Prove2me | solution 1 for GlobalTheory.SCV.hasSumLocallyUniformlyOn_of_locally_normal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:41.190803+00:00
-- url     : https://prove2.me/submissions/6aabb562-2974-4494-b13b-1aef9df6cf2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} {l : Filter ι} {F : ι → E → V} {f : E → V} {U : Set E}
omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℂ V]
namespace GlobalTheory.SCV
theorem _root_.solution
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i) :
    HasSumLocallyUniformlyOn F (fun z => ∑' i, F i z) U := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn]
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx => ?_
  obtain ⟨t, ht, u, hu, h⟩ := hle x hx
  exact ⟨t, nhdsWithin_le_nhds ht, tendstoUniformlyOn_tsum hu h⟩
end GlobalTheory.SCV
