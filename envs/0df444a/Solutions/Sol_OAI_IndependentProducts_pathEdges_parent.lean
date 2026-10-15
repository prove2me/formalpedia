-- Prove2me | solution 1 for OAI.IndependentProducts.pathEdges_parent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:29:03.344923+00:00
-- url     : https://prove2.me/submissions/b8647c84-342f-47c4-a313-d52bf86ed351

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/FiniteHeads.lean:L138-L154
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.pathEdges_parent. The node keeps its source
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
import Theorems.Thm_OAI_IndependentProducts_mem_pathEdges_iff

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

lemma pathEdges_parent (e : Edge) : pathEdges e.val = insert e (pathEdges e.val.dropLast) := by
  classical
  ext f
  simp only [Finset.mem_insert, mem_pathEdges_iff]
  constructor
  · intro h
    by_cases he : f = e
    · exact Or.inl he
    · right
      rw [List.dropLast_eq_take]
      refine List.prefix_take_iff.mpr ⟨h, ?_⟩
      have hl := h.length_le
      have hn : f.val.length ≠ e.val.length := fun hp => he (Subtype.ext (h.eq_of_length hp))
      omega
  · rintro (rfl | h)
    · exact List.prefix_rfl
    · exact h.trans (List.dropLast_prefix _)

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

theorem solution (e : Edge) : pathEdges e.val = insert e (pathEdges e.val.dropLast) := by
  first
    | exact OAI.IndependentProducts.pathEdges_parent e
    | exact OAI.IndependentProducts.pathEdges_parent
    | (apply OAI.IndependentProducts.pathEdges_parent <;> assumption)
    | (intros; apply OAI.IndependentProducts.pathEdges_parent <;> assumption)
