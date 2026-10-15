-- Prove2me | solution 1 for OAI.IndependentProducts.map_gaussian_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:09:28.570564+00:00
-- url     : https://prove2.me/submissions/d8dfc879-9d9f-475e-8b0a-235f94d3a4d8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/ScalarBounds.lean:L263-L279
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.map_gaussian_weighted_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds

-- ---- from OAI.Analysis.ProductSpaces.ScalarBounds ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts

section SecondMoment
variable {Ω : Type uΩ} [MeasurableSpace Ω] {μ : Measure Ω}

variable [IsProbabilityMeasure μ]

end SecondMoment
end IndependentProducts

namespace IndependentProducts

section GaussianSum
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [DecidableEq ι]
  {P : Measure Ω} [IsProbabilityMeasure P]

lemma map_gaussian_finset_sum (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (v : ι → ℝ≥0) (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i))
    (s : Finset ι) : P.map (fun ω => ∑ i ∈ s, X i ω) = gaussianReal 0 (∑ i ∈ s, v i) := by
  induction s using Finset.induction_on with
  | empty => simp [Measure.map_const, gaussianReal_zero_var]
  | @insert i s hi ih =>
    have hind' := (hind.indepFun_finsetSum_of_notMem hX hi).symm
    have hsum := gaussianReal_add_gaussianReal_of_indepFun hind'
      (hlaw i)
      (by simpa only [Finset.sum_fn] using ih)
    simpa only [Finset.sum_insert hi, Finset.sum_fn, Pi.add_def, zero_add] using hsum

variable [Fintype ι]

lemma map_gaussian_weighted_sum (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x => ∑ i, a i * x i) =
      gaussianReal 0 (∑ i, NNReal.mk (a i ^ 2) (sq_nonneg _)) := by
  let P := Measure.pi (fun _ : ι => gaussianReal 0 1)
  have hind : iIndepFun (fun i : ι => fun x : ι → ℝ => a i * x i) P :=
    iIndepFun_pi (fun i => (measurable_const.mul measurable_id).aemeasurable)
  have hlaw : ∀ i, P.map (fun x => a i * x i) = gaussianReal 0 (NNReal.mk (a i ^ 2) (sq_nonneg _)) := by
    intro i
    have he : (fun x : ι → ℝ => a i * x i) = (fun z => a i * z) ∘ Function.eval i := rfl
    rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq,
      gaussianReal_map_const_mul]
    apply congrArg₂ gaussianReal
    · simp
    · ext
      change a i ^ 2 * 1 = a i ^ 2
      ring
  exact map_gaussian_finset_sum _ (fun _ => by fun_prop) hind _ hlaw Finset.univ

end GaussianSum
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uΩ uι
variable {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω] [DecidableEq ι]
  {P : Measure Ω} [IsProbabilityMeasure P]
variable [Fintype ι]

theorem solution (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x => ∑ i, a i * x i) =
      gaussianReal 0 (∑ i, NNReal.mk (a i ^ 2) (sq_nonneg _)) := by
  first
    | exact OAI.IndependentProducts.map_gaussian_weighted_sum a
    | exact OAI.IndependentProducts.map_gaussian_weighted_sum
    | (apply OAI.IndependentProducts.map_gaussian_weighted_sum <;> assumption)
    | (intros; apply OAI.IndependentProducts.map_gaussian_weighted_sum <;> assumption)
