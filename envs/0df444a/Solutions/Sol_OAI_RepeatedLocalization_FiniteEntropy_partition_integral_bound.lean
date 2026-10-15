-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.partition_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:27:27.345156+00:00
-- url     : https://prove2.me/submissions/36cd84f9-0078-44ab-9b68-529128b3f2b8

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/CountableIntegrals.lean:L79-L96
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.partition_integral_bound. The node keeps its source
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

lemma partition_integral_bound {α ι : Type*} [MeasurableSpace α] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] (μ : Measure α)
    (L : α → ι) (hL : Measurable L) {f g : α → ℝ} (hf0 : ∀ x,0 ≤ f x)
    (hf : ∀ i,IntegrableOn f {x | L x = i} μ) (hg : Integrable g μ)
    (hb : ∀ i,(∫ x in {x | L x = i},f x ∂μ) ≤ ∫ x in {x | L x = i},g x ∂μ) :
    Integrable f μ ∧ (∫ x,f x ∂μ) ≤ ∫ x,g x ∂μ := by
  have hsumG := hasSum_integral_fibers μ hL hg
  have hsum : Summable (fun i => ∫ x in {x | L x = i},f x ∂μ) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg hf0) hb hsumG.summable
  have hInt : Integrable f μ := by
    have hs : IntegrableOn f (⋃ i,{x | L x = i}) μ :=
      integrableOn_iUnion_of_summable_integral_norm hf (by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hf0 _)] using hsum)
    simpa only [fiber_union,integrableOn_univ] using hs
  refine ⟨hInt,?_⟩
  have hsumF := hasSum_integral_fibers μ hL hInt
  rw [← hsumF.tsum_eq,← hsumG.tsum_eq]
  exact Summable.tsum_le_tsum hb hsumF.summable hsumG.summable

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {α ι : Type*} [MeasurableSpace α] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] (μ : Measure α)
    (L : α → ι) (hL : Measurable L) {f g : α → ℝ} (hf0 : ∀ x,0 ≤ f x)
    (hf : ∀ i,IntegrableOn f {x | L x = i} μ) (hg : Integrable g μ)
    (hb : ∀ i,(∫ x in {x | L x = i},f x ∂μ) ≤ ∫ x in {x | L x = i},g x ∂μ) :
    Integrable f μ ∧ (∫ x,f x ∂μ) ≤ ∫ x,g x ∂μ := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.partition_integral_bound μ L hL hf0 hf hg hb
    | exact OAI.RepeatedLocalization.FiniteEntropy.partition_integral_bound
    | (apply OAI.RepeatedLocalization.FiniteEntropy.partition_integral_bound <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.partition_integral_bound <;> assumption)
