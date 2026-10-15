-- Prove2me | solution 1 for OAI.RuledApproximation.inter_reciprocal_cthickening
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:31:42.394535+00:00
-- url     : https://prove2.me/submissions/d689995d-968b-4150-a71f-b42c8156a5e0

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/OuterApproximation.lean:L12-L26
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.inter_reciprocal_cthickening. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation

-- ---- from OAI.Geometry.RuledCovering.OuterApproximation ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Closed outer neighborhoods recover a closed set even when its frontier has positive measure. -/
lemma inter_reciprocal_cthickening {E : Type*} [MetricSpace E] (K : Set E)
    (hK : IsClosed K) :
    (⋂ n : ℕ, cthickening (1 / ((n : ℝ) + 1)) K) = K := by
  apply Subset.antisymm
  · intro x hx
    have hxn : ∀ n : ℕ, infEDist x K ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      simpa only [mem_iInter, mem_cthickening_iff] using hx
    have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hz : infEDist x K = 0 := le_antisymm (ge_of_tendsto ht (.of_forall hxn)) bot_le
    exact hK.closure_subset (mem_closure_iff_infEDist_zero.mpr hz)
  · exact subset_iInter fun _ => self_subset_cthickening K

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.inter_reciprocal_cthickening := @_root_.OAI.RuledApproximation.inter_reciprocal_cthickening
