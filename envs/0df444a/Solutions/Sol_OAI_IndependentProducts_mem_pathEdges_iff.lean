-- Prove2me | solution 1 for OAI.IndependentProducts.mem_pathEdges_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:27:08.87725+00:00
-- url     : https://prove2.me/submissions/7682b6dc-1f20-4916-a99e-79e90de52a93

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/FiniteHeads.lean:L118-L129
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.mem_pathEdges_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads

-- ---- from OAI.Analysis.ProductSpaces.FiniteHeads ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uκ

namespace IndependentProducts
namespace FiniteHead
variable (T : FiniteHead)

end FiniteHead
end IndependentProducts

namespace IndependentProducts

lemma mem_pathEdges_iff (v : Vertex) (e : Edge) : e ∈ pathEdges v ↔ e.val <+: v := by
  classical
  simp only [pathEdges, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, rfl⟩
    exact List.take_prefix _ _
  · intro h
    have hlen : 0 < e.val.length := List.length_pos_iff.mpr e.property
    refine ⟨⟨e.val.length - 1, by have := h.length_le; omega⟩, ?_⟩
    apply Subtype.ext
    change v.take (e.val.length - 1 + 1) = e.val
    rw [Nat.sub_add_cancel (by omega), ← List.prefix_iff_eq_take.mp h]

section Selector
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

end Selector
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uκ

theorem solution (v : Vertex) (e : Edge) : e ∈ pathEdges v ↔ e.val <+: v := by
  first
    | exact OAI.IndependentProducts.mem_pathEdges_iff v e
    | exact OAI.IndependentProducts.mem_pathEdges_iff
    | (apply OAI.IndependentProducts.mem_pathEdges_iff <;> assumption)
    | (intros; apply OAI.IndependentProducts.mem_pathEdges_iff <;> assumption)
