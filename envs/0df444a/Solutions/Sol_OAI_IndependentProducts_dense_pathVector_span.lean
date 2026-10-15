-- Prove2me | solution 1 for OAI.IndependentProducts.dense_pathVector_span
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:35:02.968135+00:00
-- url     : https://prove2.me/submissions/033de13f-65b7-4201-adf4-125f7b498daa

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ClosedTails.lean:L25-L41
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.dense_pathVector_span. The node keeps its source
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

-- ---- from OAI.Analysis.ProductSpaces.ClosedTails ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace IndependentProducts
section Tails
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)

lemma path_generator_set_eq :
    {f : Lp ℝ 1 (productMeasure μ) | ∃ v : Vertex,
      (f : Sample → ℝ) =ᵐ[productMeasure μ] pathProduct v} = Set.range (pathL1 μ h₂) := by
  ext f
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    exact Lp.ext ((pathL1_ae μ h₂ v).trans hv.symm)
  · rintro ⟨v, rfl⟩
    exact ⟨v, pathL1_ae μ h₂ v⟩

lemma dense_pathVector_span :
    Dense ((Submodule.span ℝ (Set.range (pathVector μ h₂))) : Set (productSpan μ)) := by
  apply Subtype.dense_iff.mpr
  have he : ((↑) : productSpan μ → Lp ℝ 1 (productMeasure μ)) ''
      (Submodule.span ℝ (Set.range (pathVector μ h₂)) : Set (productSpan μ)) =
      (Submodule.span ℝ (Set.range (pathL1 μ h₂)) : Set (Lp ℝ 1 (productMeasure μ))) := by
    change (↑((Submodule.span ℝ (Set.range (pathVector μ h₂))).map (productSpan μ).subtype) :
      Set (Lp ℝ 1 (productMeasure μ))) = _
    rw [Submodule.map_span]
    congr 2
    rw [← Set.range_comp]
    rfl
  intro x hx
  change x ∈ closure (((↑) : productSpan μ → Lp ℝ 1 (productMeasure μ)) ''
    (Submodule.span ℝ (Set.range (pathVector μ h₂)) : Set (productSpan μ)))
  rw [he]
  simpa only [productSpan, path_generator_set_eq μ h₂, Submodule.topologicalClosure_coe] using hx

namespace FiniteHead
variable (T : FiniteHead)

end FiniteHead
end Tails
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)

theorem solution :
    Dense ((Submodule.span ℝ (Set.range (pathVector μ h₂))) : Set (productSpan μ)) := by
  first
    | exact OAI.IndependentProducts.dense_pathVector_span μ h₂
    | exact OAI.IndependentProducts.dense_pathVector_span
    | (apply OAI.IndependentProducts.dense_pathVector_span <;> assumption)
    | (intros; apply OAI.IndependentProducts.dense_pathVector_span <;> assumption)
