-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Experiment.integral_pmf_bind
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:20:15.759847+00:00
-- url     : https://prove2.me/submissions/58fac79a-f91f-425c-80c9-f4b0413d765c

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/DiscreteLaw.lean:L135-L150
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Experiment.integral_pmf_bind. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw

-- ---- from OAI.Probability.ThreeStateClauses.DiscreteLaw ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Discrete Law. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α : Type*}

section Measures
variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

end Measures

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

lemma pmf_bounded_integrable (p : PMF α) {f : α → ℝ} {C : ℝ} (hf : ∀ a, |f a| ≤ C) :
    Integrable f p.toMeasure :=
  Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun a ↦ by simpa only [Real.norm_eq_abs] using hf a))

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSingletonClass β] in
lemma pmf_measure_bind (p : PMF α) (K : α → PMF β) :
    (p.bind K).toMeasure = Measure.sum (fun a ↦ p a • (K a).toMeasure) := by
  apply Measure.ext
  intro s hs
  rw [PMF.toMeasure_bind_apply _ _ _ hs, Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul]

lemma integral_pmf_bind (p : PMF α) (K : α → PMF β) {f : β → ℝ} {C : ℝ}
    (hf : ∀ b, |f b| ≤ C) :
    (∫ b, f b ∂(p.bind K).toMeasure) = ∫ a, (∫ b, f b ∂(K a).toMeasure) ∂p.toMeasure := by
  have hi := pmf_bounded_integrable (p.bind K) hf
  rw [pmf_measure_bind] at hi ⊢
  rw [integral_sum_measure hi]
  simp only [integral_smul_measure, smul_eq_mul]
  rw [PMF.integral_eq_tsum]
  · rfl
  · apply pmf_bounded_integrable
    intro a
    calc
      |∫ b, f b ∂(K a).toMeasure| ≤ ∫ b, |f b| ∂(K a).toMeasure := abs_integral_le_integral_abs
      _ ≤ ∫ _, C ∂(K a).toMeasure := integral_mono (pmf_bounded_integrable (K a) hf).abs
        (integrable_const C) hf
      _ = C := by simp

end ThreeState.TreeClauses.Experiment

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Experiment
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators ENNReal
open ThreeState.TreeClauses.Radial


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Experiment.integral_pmf_bind := @_root_.OAI.ThreeState.TreeClauses.Experiment.integral_pmf_bind
