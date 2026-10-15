-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.countable_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:26:14.304434+00:00
-- url     : https://prove2.me/submissions/0f97fd38-26c0-4b40-b02c-fe666c9ec00f

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/CountableIntegrals.lean:L50-L77
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.countable_cost_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards

-- ---- from OAI.Probability.Localization.CountableIntegrals ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma fiber_union {α ι : Type*} (L : α → ι) : (⋃ i,{x | L x = i}) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  exact ⟨L x,rfl⟩

lemma fiber_pairwise {α ι : Type*} (L : α → ι) :
    Pairwise (fun i j => Disjoint {x | L x = i} {x | L x = j}) := by
  intro i j hij
  exact Set.disjoint_left.mpr (fun x hi hj => hij (hi.symm.trans hj))

lemma hasSum_integral_fibers {α ι : Type*} [MeasurableSpace α] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] (μ : Measure α) {L : α → ι}
    (hL : Measurable L) {g : α → ℝ} (hg : Integrable g μ) :
    HasSum (fun i => ∫ x in {x | L x = i},g x ∂μ) (∫ x,g x ∂μ) := by
  simpa only [fiber_union,Measure.restrict_univ] using hasSum_integral_iUnion (s := fun i => {x | L x = i})
    (fun i => hL (measurableSet_singleton i)) (fiber_pairwise L) hg.integrableOn

lemma integral_comp_fiber {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (L : α → ι) (F : ι → ℝ) (i : ι) (hi : MeasurableSet {x | L x = i}) :
    (∫ x in {x | L x = i},F (L x) ∂μ) = (μ {x | L x = i}).toReal * F i := by
  rw [setIntegral_congr_fun hi (fun x hx => congrArg F hx)]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul]

lemma integrableOn_comp_fiber {α ι : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (L : α → ι) (F : ι → ℝ) (i : ι) (hi : MeasurableSet {x | L x = i}) :
    IntegrableOn (fun x => F (L x)) {x | L x = i} μ :=
  (integrableOn_const (C := F i) (s := {x | L x = i})).congr_fun (fun x hx => (congrArg F hx).symm) hi

lemma countable_cost_bound {α ι : Type*} [MeasurableSpace α] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] (μ : Measure α) [IsFiniteMeasure μ]
    (L : α → ι) (hL : Measurable L) (F : ι → ℝ) (hF : ∀ i,0 ≤ F i)
    {g : α → ℝ} (hg : Integrable g μ)
    (hb : ∀ i,(μ {x | L x = i}).toReal * F i ≤ ∫ x in {x | L x = i},g x ∂μ) :
    Integrable (fun x => F (L x)) μ ∧ (∫ x,F (L x) ∂μ) ≤ ∫ x,g x ∂μ := by
  have hsumG := hasSum_integral_fibers μ hL hg
  have hnon (i : ι) : 0 ≤ (μ {x | L x = i}).toReal * F i := mul_nonneg ENNReal.toReal_nonneg (hF i)
  have hsum : Summable (fun i => (μ {x | L x = i}).toReal * F i) :=
    Summable.of_nonneg_of_le hnon hb hsumG.summable
  have hInt : Integrable (fun x => F (L x)) μ := by
    have hs := integrableOn_iUnion_of_summable_integral_norm
      (fun i => integrableOn_comp_fiber μ L F i (hL (measurableSet_singleton i)))
    apply (integrableOn_univ.mp ?_)
    rw [← fiber_union L]
    apply hs
    have he (i : ι) : (∫ x in {x | L x = i},‖F (L x)‖ ∂μ) =
        (μ {x | L x = i}).toReal * F i := by
      rw [integral_comp_fiber μ L (fun j => ‖F j‖) i (hL (measurableSet_singleton i))]
      rw [Real.norm_eq_abs,abs_of_nonneg (hF i)]
    simpa only [he] using hsum
  refine ⟨hInt,?_⟩
  have hsumF := hasSum_integral_fibers μ hL hInt
  rw [← hsumF.tsum_eq,← hsumG.tsum_eq]
  apply Summable.tsum_le_tsum _ hsumF.summable hsumG.summable
  intro i
  rw [integral_comp_fiber μ L F i (hL (measurableSet_singleton i))]
  exact hb i

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {α ι : Type*} [MeasurableSpace α] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] (μ : Measure α) [IsFiniteMeasure μ]
    (L : α → ι) (hL : Measurable L) (F : ι → ℝ) (hF : ∀ i,0 ≤ F i)
    {g : α → ℝ} (hg : Integrable g μ)
    (hb : ∀ i,(μ {x | L x = i}).toReal * F i ≤ ∫ x in {x | L x = i},g x ∂μ) :
    Integrable (fun x => F (L x)) μ ∧ (∫ x,F (L x) ∂μ) ≤ ∫ x,g x ∂μ := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.countable_cost_bound μ L hL F hF hg hb
    | exact OAI.RepeatedLocalization.FiniteEntropy.countable_cost_bound
    | (apply OAI.RepeatedLocalization.FiniteEntropy.countable_cost_bound <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.countable_cost_bound <;> assumption)
