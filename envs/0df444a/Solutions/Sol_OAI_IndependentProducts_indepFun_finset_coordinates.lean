-- Prove2me | solution 1 for OAI.IndependentProducts.indepFun_finset_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:00:48.163881+00:00
-- url     : https://prove2.me/submissions/90c2799b-bb06-4a63-a618-b780b79f7d61

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/PathMoments.lean:L227-L249
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.indepFun_finset_coordinates. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments

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

end CoordinateProducts
end IndependentProducts

namespace IndependentProducts

section ChildMoments
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma indepFun_finset_coordinates (s : Finset Edge) (f : Edge → ℝ → ℝ)
    (hf : ∀ e, Measurable (f e)) (e : Edge) (he : e ∉ s) :
    IndepFun (fun ω : Sample => ∏ i ∈ s, f i (ω i)) (fun ω : Sample => ω e)
      (productMeasure μ) := by
  classical
  let g : Edge → ℝ → ℝ := fun i => if i = e then id else f i
  have gmeas : ∀ i, Measurable (g i) := fun i => by
    dsimp [g]
    split_ifs
    · exact measurable_id
    · exact hf i
  have hi : iIndepFun (fun i : Edge => fun ω : Sample => g i (ω i)) (productMeasure μ) :=
    iIndepFun_infinitePi gmeas
  have hh := hi.indepFun_finsetProd_of_notMem
    (fun i => (gmeas i).comp (measurable_pi_apply i)) he
  have hg : (∏ i ∈ s, fun ω : Sample => g i (ω i)) = fun ω => ∏ i ∈ s, f i (ω i) := by
    funext ω
    simp only [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro i hi
    have hie : i ≠ e := fun hie => he (hie ▸ hi)
    simp [g, hie]
  rwa [hg, show (fun ω : Sample => g e (ω e)) = (fun ω => ω e) by simp [g]] at hh

end ChildMoments
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

theorem solution (s : Finset Edge) (f : Edge → ℝ → ℝ)
    (hf : ∀ e, Measurable (f e)) (e : Edge) (he : e ∉ s) :
    IndepFun (fun ω : Sample => ∏ i ∈ s, f i (ω i)) (fun ω : Sample => ω e)
      (productMeasure μ) := by
  first
    | exact OAI.IndependentProducts.indepFun_finset_coordinates s f hf e he
    | exact OAI.IndependentProducts.indepFun_finset_coordinates μ s f hf e he
    | exact OAI.IndependentProducts.indepFun_finset_coordinates
    | (apply OAI.IndependentProducts.indepFun_finset_coordinates <;> assumption)
    | (intros; apply OAI.IndependentProducts.indepFun_finset_coordinates <;> assumption)
