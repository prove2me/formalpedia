-- Prove2me | solution 1 for OAI.IndependentProducts.FiniteHead.boundary_eq_of_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:25:25.695527+00:00
-- url     : https://prove2.me/submissions/ed677994-416a-43c8-827b-8a1a07e4bb85

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/FiniteHeads.lean:L25-L36
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.FiniteHead.boundary_eq_of_prefix. The node keeps its source
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

lemma boundary_eq_of_prefix {e f : T.Boundary} (h : e.val.val <+: f.val.val) : e = f := by
  apply Subtype.ext
  apply Subtype.ext
  by_contra hne
  have hlen : e.val.val.length < f.val.val.length := by
    have hle := h.length_le
    have hn : e.val.val.length ≠ f.val.val.length := fun he => hne (h.eq_of_length he)
    omega
  have hp : e.val.val <+: f.val.val.dropLast := by
    rw [List.dropLast_eq_take]
    exact List.prefix_take_iff.mpr ⟨h, by omega⟩
  exact e.property.1 (T.prefix_mem hp f.property.2)

end FiniteHead
end IndependentProducts

namespace IndependentProducts

section Selector
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

end Selector
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts OAI.IndependentProducts.FiniteHead
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uκ
variable (T : FiniteHead)

theorem solution {e f : T.Boundary} (h : e.val.val <+: f.val.val) : e = f := by
  first
    | exact OAI.IndependentProducts.FiniteHead.boundary_eq_of_prefix h
    | exact OAI.IndependentProducts.FiniteHead.boundary_eq_of_prefix T h
    | exact OAI.IndependentProducts.FiniteHead.boundary_eq_of_prefix
    | (apply OAI.IndependentProducts.FiniteHead.boundary_eq_of_prefix <;> assumption)
    | (intros; apply OAI.IndependentProducts.FiniteHead.boundary_eq_of_prefix <;> assumption)
