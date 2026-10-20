-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Experiment.discrete_degradation_centered
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:24:04.724178+00:00
-- url     : https://prove2.me/submissions/f3643301-c36e-4e72-9760-2b7bd4915765

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/Degradation.lean:L76-L90
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Experiment.discrete_degradation_centered. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_integral_pmf_bind

-- ---- from OAI.Probability.ThreeStateClauses.PosteriorLaw ----
namespace OAI

/-! Posterior Law. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open Radial ThreeState.TreeClauses.Positive
open Radial

lemma coordinate_nonneg (m : Message) (i : Fin 3) : 0 ≤ m.1 i := m.2.1 i
end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Experiment

end

end OAI

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

lemma discreteMarginal_apply (p : Fin 3 → PMF α) (a : α) :
    discreteMarginal p a = (p 0 a+p 1 a+p 2 a)/3 := by
  simp [discreteMarginal, PMF.bind_apply, tsum_fintype, Fin.sum_univ_three, div_eq_mul_inv]
  ring

lemma discreteMarginal_real (p : Fin 3 → PMF α) (a : α) :
    (discreteMarginal p a).toReal = discreteWeight p a := by
  rw [discreteMarginal_apply, ENNReal.toReal_div,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨(p 0).apply_ne_top a, (p 1).apply_ne_top a⟩)
      ((p 2).apply_ne_top a),
    ENNReal.toReal_add ((p 0).apply_ne_top a) ((p 1).apply_ne_top a)]
  norm_num [discreteWeight, avg]

lemma discreteWeight_zero (p : Fin 3 → PMF α) (a : α) (h : discreteWeight p a = 0) (i : Fin 3) :
    (p i a).toReal = 0 := by
  dsimp [discreteWeight, avg] at h
  fin_cases i <;> dsimp <;> linarith [ENNReal.toReal_nonneg (a := p 0 a),
    ENNReal.toReal_nonneg (a := p 1 a), ENNReal.toReal_nonneg (a := p 2 a)]

lemma discrete_bayes (p : Fin 3 → PMF α) (a : α) (i : Fin 3) :
    discreteWeight p a*(discreteMessage p a).1 i = (p i a).toReal := by
  unfold discreteMessage
  split_ifs with h
  · simpa [h] using (discreteWeight_zero p a h i).symm
  · exact mul_div_cancel₀ _ h

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

lemma integral_pmf_map (p : PMF α) (T : α → β) (f : β → ℝ) :
    (∫ b, f b ∂(p.map T).toMeasure) = ∫ a, f (T a) ∂p.toMeasure := by
  rw [← PMF.toMeasure_map T p (measurable_of_countable T)]
  exact integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable

lemma discrete_bayes_integral (p : Fin 3 → PMF α) (i : Fin 3) {g : α → ℝ} {C : ℝ}
    (hg : ∀ a, |g a| ≤ C) :
    (∫ a, (discreteMessage p a).1 i*g a ∂(discreteMarginal p).toMeasure) =
      ∫ a, g a ∂(p i).toMeasure := by
  rw [PMF.integral_eq_tsum, PMF.integral_eq_tsum _ _ (pmf_bounded_integrable (p i) hg)]
  · apply tsum_congr
    intro a
    simp only [smul_eq_mul, discreteMarginal_real, ← mul_assoc, discrete_bayes]
  · apply pmf_bounded_integrable (C := 3*C)
    intro a
    rw [abs_mul, abs_of_nonneg (coordinate_nonneg _ _)]
    exact mul_le_mul (coordinate_le_three _ _) (hg a) (abs_nonneg _) (by norm_num)

end ThreeState.TreeClauses.Experiment

end

end OAI

-- ---- from OAI.Probability.ThreeStateClauses.Degradation ----
namespace OAI

/-! Degradation. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α β : Type*}

lemma kernelJoint_snd (p : PMF α) (K : α → PMF β) :
    (kernelJoint p K).map Prod.snd = p.bind K := by
  simp only [kernelJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have h (a : α) : ((K a).map (fun b ↦ b)) = K a := PMF.map_id _
  simp only [h]

lemma discreteMarginal_bind (p : Fin 3 → PMF α) (K : α → PMF β) :
    discreteMarginal (fun i ↦ (p i).bind K) = (discreteMarginal p).bind K := by
  simp only [discreteMarginal, PMF.bind_bind]

section Measures
variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

lemma integral_kernelJoint (p : PMF α) (K : α → PMF β) {f : α × β → ℝ} {C : ℝ}
    (hf : ∀ z, |f z| ≤ C) :
    (∫ z, f z ∂(kernelJoint p K).toMeasure) =
      ∫ a, (∫ b, f (a,b) ∂(K a).toMeasure) ∂p.toMeasure := by
  rw [kernelJoint, integral_pmf_bind p _ hf]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun a ↦ integral_pmf_map (K a) _ f)

lemma integral_kernelJoint_snd (p : PMF α) (K : α → PMF β) (f : β → ℝ) :
    (∫ z, f z.2 ∂(kernelJoint p K).toMeasure) = ∫ b, f b ∂(p.bind K).toMeasure := by
  rw [← integral_pmf_map, kernelJoint_snd]

lemma discrete_degradation_identity (p : Fin 3 → PMF α) (K : α → PMF β) (i : Fin 3)
    {g : β → ℝ} {C : ℝ} (hg : ∀ b, |g b| ≤ C) :
    (∫ z, (discreteMessage p z.1).1 i*g z.2 ∂(kernelJoint (discreteMarginal p) K).toMeasure) =
      ∫ b, (discreteMessage (fun j ↦ (p j).bind K) b).1 i*g b
        ∂(discreteMarginal (fun j ↦ (p j).bind K)).toMeasure := by
  have hb (z : α × β) : |(discreteMessage p z.1).1 i*g z.2| ≤ 3*C := by
    rw [abs_mul, abs_of_nonneg (coordinate_nonneg _ _)]
    exact mul_le_mul (coordinate_le_three _ _) (hg z.2) (abs_nonneg _) (by norm_num)
  rw [integral_kernelJoint _ _ hb]
  simp only [integral_const_mul]
  have hbound (a : α) : |∫ b, g b ∂(K a).toMeasure| ≤ C := by
    calc
      |∫ b, g b ∂(K a).toMeasure| ≤ ∫ b, |g b| ∂(K a).toMeasure := abs_integral_le_integral_abs
      _ ≤ ∫ _, C ∂(K a).toMeasure := integral_mono (pmf_bounded_integrable (K a) hg).abs
        (integrable_const C) hg
      _ = C := by simp
  rw [discrete_bayes_integral p i hbound, discrete_bayes_integral _ i hg,
    integral_pmf_bind (p i) K hg]

lemma discrete_degradation_centered (p : Fin 3 → PMF α) (K : α → PMF β) (i : Fin 3)
    {g : β → ℝ} {C : ℝ} (hg : ∀ b, |g b| ≤ C) :
    (∫ z, ((discreteMessage p z.1).1 i-(discreteMessage (fun j ↦ (p j).bind K) z.2).1 i)*g z.2
      ∂(kernelJoint (discreteMarginal p) K).toMeasure) = 0 := by
  have hb (m : Message) (b : β) : |m.1 i*g b| ≤ 3*C := by
    rw [abs_mul, abs_of_nonneg (coordinate_nonneg _ _)]
    exact mul_le_mul (coordinate_le_three _ _) (hg b) (abs_nonneg _) (by norm_num)
  simp_rw [sub_mul]
  rw [integral_sub (f := fun z : α × β ↦ (discreteMessage p z.1).1 i*g z.2)
    (g := fun z : α × β ↦ (discreteMessage (fun j ↦ (p j).bind K) z.2).1 i*g z.2)
    (pmf_bounded_integrable _ (fun z ↦ hb _ z.2))
    (pmf_bounded_integrable _ (fun z ↦ hb _ z.2)),
    discrete_degradation_identity p K i hg,
    integral_kernelJoint_snd (f := fun b ↦ (discreteMessage (fun j ↦ (p j).bind K) b).1 i*g b),
    ← discreteMarginal_bind, sub_self]

end Measures
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


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Experiment.discrete_degradation_centered := @_root_.OAI.ThreeState.TreeClauses.Experiment.discrete_degradation_centered
