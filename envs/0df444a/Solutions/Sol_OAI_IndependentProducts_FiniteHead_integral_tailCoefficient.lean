-- Prove2me | solution 1 for OAI.IndependentProducts.FiniteHead.integral_tailCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:39:50.196065+00:00
-- url     : https://prove2.me/submissions/4cb6a6b1-a63d-48bc-a9ed-583ed9892848

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/TailCoefficients.lean:L136-L155
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.FiniteHead.integral_tailCoefficient. The node keeps its source
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
import Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients

-- ---- from OAI.Analysis.ProductSpaces.PathMoments ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section CoordinateProducts

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma integral_coordinates_prod {ι : Type uι} [Fintype ι]
    (e : ι → Edge) (he : Function.Injective e) (f : ι → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) :
    (∫ ω : Sample, ∏ i, f i (ω (e i)) ∂productMeasure μ) = ∏ i, ∫ w, f i w ∂μ := by
  let hmp := measurePreserving_coordinates μ e he
  have hg : AEStronglyMeasurable (fun x : ι → ℝ => ∏ i, f i (x i))
      ((productMeasure μ).map (fun ω : Sample => fun i => ω (e i))) := by
    exact (Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))).aestronglyMeasurable
  rw [← integral_map hmp.measurable.aemeasurable hg, hmp.map_eq,
    integral_fintype_prod_eq_prod]

lemma integrable_finset_coordinates_prod (s : Finset Edge) (f : Edge → ℝ → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun ω : Sample => ∏ i ∈ s, f i (ω i)) (productMeasure μ) := by
  have hi := integrable_coordinates_prod μ (fun i : s => i.val) Subtype.val_injective
    (fun i : s => f i) (fun i => hf i i.property)
  have he : (fun ω : Sample => ∏ i : s, f i (ω i)) = fun ω => ∏ i ∈ s, f i (ω i) :=
    funext (fun ω => s.prod_coe_sort (fun i => f i (ω i)))
  rwa [he] at hi

lemma integral_finset_coordinates_prod (s : Finset Edge) (f : Edge → ℝ → ℝ)
    (hf : ∀ i ∈ s, Measurable (f i)) :
    (∫ ω : Sample, ∏ i ∈ s, f i (ω i) ∂productMeasure μ) = ∏ i ∈ s, ∫ w, f i w ∂μ := by
  have hi := integral_coordinates_prod μ (fun i : s => i.val) Subtype.val_injective
    (fun i : s => f i) (fun i => hf i i.property)
  have he : (fun ω : Sample => ∏ i : s, f i (ω i)) = fun ω => ∏ i ∈ s, f i (ω i) :=
    funext (fun ω => s.prod_coe_sort (fun i => f i (ω i)))
  rw [he, s.prod_coe_sort (fun i => ∫ w, f i w ∂μ)] at hi
  exact hi

end CoordinateProducts
end IndependentProducts

namespace IndependentProducts

section ChildMoments
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

end ChildMoments
end IndependentProducts

end

end OAI

-- ---- from OAI.Analysis.ProductSpaces.TailCoefficients ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι uκ

namespace IndependentProducts
section FiniteRepresentatives
variable (μ : Measure ℝ) [hμprob : IsProbabilityMeasure μ]
  (h₂ : MemLp (fun w : ℝ => w) 2 μ)

namespace FiniteHead
variable (T : FiniteHead)

end FiniteHead
end FiniteRepresentatives

lemma integrable_residualProduct (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : Integrable (fun w : ℝ => w) μ) (v : Vertex) (e : Edge) :
    Integrable (residualProduct v e) (productMeasure μ) :=
  integrable_finset_coordinates_prod μ _ _ (fun _ _ => hw)

lemma integral_residualProduct (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : ∫ w : ℝ, w ∂μ = 1) (v : Vertex) (e : Edge) :
    ∫ ω, residualProduct v e ω ∂productMeasure μ = 1 := by
  change (∫ ω : Sample, ∏ d ∈ pathEdges v \ pathEdges e.val, ω d ∂productMeasure μ) = 1
  rw [integral_finset_coordinates_prod μ _ (fun _ w => w) (by fun_prop)]
  simp only [hm, Finset.prod_const_one]

namespace FiniteHead
section FiniteTailData
variable {ι : Type uι} {κ : Type uκ} [hιfinite : Fintype ι] [Fintype κ] [DecidableEq ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)

lemma integral_tailCoefficient {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : Integrable (fun w : ℝ => w) μ) (hm : ∫ w : ℝ, w ∂μ = 1)
    (old : Sample) (i : ι) :
    ∫ desc, T.tailCoefficient e v j a old i desc ∂productMeasure μ =
      ∑ k, if j k = i then a k * pathProduct (e i).val.val.dropLast old else 0 := by
  classical
  unfold tailCoefficient
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    split_ifs
    · rw [integral_const_mul, integral_residualProduct μ hm, mul_one]
    · simp
  · intro k hk
    split_ifs
    · exact (integrable_residualProduct μ hw _ _).const_mul _
    · exact integrable_zero _ _ _

end FiniteTailData
end FiniteHead
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts OAI.IndependentProducts.FiniteHead
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι uκ
variable {ι : Type uι} {κ : Type uκ} [hιfinite : Fintype ι] [Fintype κ] [DecidableEq ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)

theorem solution {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hw : Integrable (fun w : ℝ => w) μ) (hm : ∫ w : ℝ, w ∂μ = 1)
    (old : Sample) (i : ι) :
    ∫ desc, T.tailCoefficient e v j a old i desc ∂productMeasure μ =
      ∑ k, if j k = i then a k * pathProduct (e i).val.val.dropLast old else 0 := by
  first
    | exact OAI.IndependentProducts.FiniteHead.integral_tailCoefficient T e v j a μ hw hm old i
    | exact OAI.IndependentProducts.FiniteHead.integral_tailCoefficient T e v j a T e v j a μ hw hm old i
    | exact OAI.IndependentProducts.FiniteHead.integral_tailCoefficient
    | (apply OAI.IndependentProducts.FiniteHead.integral_tailCoefficient <;> assumption)
    | (intros; apply OAI.IndependentProducts.FiniteHead.integral_tailCoefficient <;> assumption)
