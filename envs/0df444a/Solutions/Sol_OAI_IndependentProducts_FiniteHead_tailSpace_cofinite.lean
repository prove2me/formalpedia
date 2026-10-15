-- Prove2me | solution 1 for OAI.IndependentProducts.FiniteHead.tailSpace_cofinite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:36:16.943332+00:00
-- url     : https://prove2.me/submissions/743c3f62-ad25-46c4-8728-45c91dfdf376

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ClosedTails.lean:L89-L100
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.FiniteHead.tailSpace_cofinite. The node keeps its source
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
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling
import Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails
import Theorems.Thm_OAI_IndependentProducts_dense_pathVector_span

-- ---- from OAI.Analysis.ProductSpaces.FiniteHeads ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uκ

namespace IndependentProducts
namespace FiniteHead
variable (T : FiniteHead)

lemma ancestor_mem (v : Vertex) : T.ancestor v ∈ T.vertices := by
  unfold ancestor
  split_ifs with h
  · exact h
  · exact (T.exit v h).property.2

end FiniteHead
end IndependentProducts

namespace IndependentProducts

section Selector
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

end Selector
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.ClosedTails ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace IndependentProducts
section Tails
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)

namespace FiniteHead
variable (T : FiniteHead)

lemma relativeVector_mem (v : Vertex) : T.relativeVector μ h₂ v ∈ T.tailAlgebraic μ h₂ := by
  by_cases hv : v ∈ T.vertices
  · simp [relativeVector, T.ancestor_of_mem hv]
  · exact Submodule.subset_span ⟨v, hv, rfl⟩

lemma headSpan_sup_tailSpace : T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ = ⊤ := by
  have hclosed : IsClosed (↑(T.tailSpace μ h₂ ⊔ T.headSpan μ h₂) : Set (productSpan μ)) :=
    Submodule.isClosed_sup_finiteDimensional (T.tailSpace μ h₂) (T.headSpan μ h₂)
      (Submodule.isClosed_topologicalClosure (T.tailAlgebraic μ h₂))
  have hle : Submodule.span ℝ (Set.range (pathVector μ h₂)) ≤ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    have hg : T.relativeVector μ h₂ v ∈ T.tailSpace μ h₂ :=
      Submodule.le_topologicalClosure _ (T.relativeVector_mem μ h₂ v)
    have ha : pathVector μ h₂ (T.ancestor v) ∈ T.headSpan μ h₂ :=
      Submodule.subset_span ⟨T.ancestor v, T.ancestor_mem v, rfl⟩
    have hgg : T.relativeVector μ h₂ v ∈ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ :=
      (show T.tailSpace μ h₂ ≤ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ from le_sup_left) hg
    have haa : pathVector μ h₂ (T.ancestor v) ∈ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ :=
      (show T.headSpan μ h₂ ≤ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ from le_sup_right) ha
    have hh := (T.tailSpace μ h₂ ⊔ T.headSpan μ h₂).add_mem hgg haa
    change pathVector μ h₂ v ∈ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂
    convert hh using 1
    simp only [relativeVector, sub_add_cancel]
  have hc := Submodule.topologicalClosure_minimal _ hle hclosed
  rw [Submodule.dense_iff_topologicalClosure_eq_top.mp (dense_pathVector_span μ h₂)] at hc
  exact top_le_iff.mp hc

lemma tailSpace_cofinite : T.tailSpace μ h₂ ∈ CofiniteSubspaces (productSpan μ) := by
  refine ⟨Submodule.isClosed_topologicalClosure _, ?_⟩
  refine FiniteDimensional.of_surjective (V := T.headSpan μ h₂)
    ((T.tailSpace μ h₂).mkQ.comp (T.headSpan μ h₂).subtype) ?_
  intro q
  obtain ⟨x, hx⟩ := (T.tailSpace μ h₂).mkQ_surjective q
  have hm : x ∈ T.tailSpace μ h₂ ⊔ T.headSpan μ h₂ := by rw [T.headSpan_sup_tailSpace μ h₂]; trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hm
  refine ⟨⟨v, hv⟩, ?_⟩
  change (T.tailSpace μ h₂).mkQ v = q
  have hz : (T.tailSpace μ h₂).mkQ u = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hu
  rw [← hx, ← huv, map_add, hz, zero_add]

end FiniteHead
end Tails
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts OAI.IndependentProducts.FiniteHead
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)
variable (T : FiniteHead)

theorem solution : T.tailSpace μ h₂ ∈ CofiniteSubspaces (productSpan μ) := by
  first
    | exact OAI.IndependentProducts.FiniteHead.tailSpace_cofinite μ h₂ T
    | exact OAI.IndependentProducts.FiniteHead.tailSpace_cofinite
    | (apply OAI.IndependentProducts.FiniteHead.tailSpace_cofinite <;> assumption)
    | (intros; apply OAI.IndependentProducts.FiniteHead.tailSpace_cofinite <;> assumption)
