-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Experiment.advantage_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:31:51.83044+00:00
-- url     : https://prove2.me/submissions/cfdb918f-18ac-4a34-8e31-ef27542b6be2

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/CompactLimits.lean:L407-L421
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Experiment.advantage_eq_integral. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_BranchMoments
import Definitions.Def_OAI_Probability_ThreeStateClauses_CompactLimits

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
lemma continuous_coordinate (i : Fin 3) : Continuous (fun m : Message ↦ m.1 i) :=
  (continuous_apply i).comp continuous_subtype_val

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
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

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

lemma discrete_coord {p : Fin 3 → PMF α} {a : α} (h : discreteWeight p a ≠ 0) (i : Fin 3) :
    (discreteMessage p a).1 i = (p i a).toReal/discreteWeight p a := by
  simp only [discreteMessage, dite_eq_right h]

section Measures
variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma integral_discreteProbability (p : Fin 3 → PMF α) {f : Message → ℝ} (hf : Measurable f) :
    (∫ m, f m ∂(discreteProbability p).toMeasure) =
      ∫ a, f (discreteMessage p a) ∂(discreteMarginal p).toMeasure := by
  change (∫ m, f m ∂Measure.map (discreteMessage p) (discreteMarginal p).toMeasure) = _
  exact integral_map (measurable_of_countable _).aemeasurable hf.aestronglyMeasurable

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

end ThreeState.TreeClauses.Experiment

end

end OAI

-- ---- from OAI.Probability.ThreeStateClauses.CompactLimits ----
namespace OAI

/-! Compact Limits. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

section Discrete
variable {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

end Discrete
end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
-- [generator] trimmed: open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

section Limits
-- [generator] dropped: variable {ι : Type*} {F : Filter ι} [F.NeBot] {Q : ι → Law} {P : ProbabilityMeasure Message}

end Limits

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

lemma continuous_tvMessage : Continuous tvMessage :=
  (continuous_avg.comp (continuous_pi (fun i ↦ ((continuous_coordinate i).sub continuous_const).abs))).div_const 2

lemma tvMessage_nonneg (m : Message) : 0 ≤ tvMessage m := by
  dsimp [tvMessage, avg]; positivity

lemma tvMessage_formula (m : Message) :
    tvMessage m = (∑ i : Spin, |m.1 i/3-(1/3:ℝ)|)/2 := by
  simp only [tvMessage, avg, ← sub_div, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 3), Fin.sum_univ_three]
  ring

lemma main_marginal_eq (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (o : Observation ℓ) :
    marginalWeight lam hlam offspring ℓ o = discreteMarginal (observationLaw lam hlam offspring ℓ) o := by
  simp only [marginalWeight, jointWeight, discreteMarginal, PMF.bind_apply, tsum_fintype, uniformSpin_apply]

lemma main_posterior_eq (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (o : Observation ℓ) (ho : discreteWeight (observationLaw lam hlam offspring ℓ) o ≠ 0) (i : Spin) :
    posterior lam hlam offspring ℓ o i = (discreteMessage (observationLaw lam hlam offspring ℓ) o).1 i/3 := by
  rw [posterior, ENNReal.toReal_div, main_marginal_eq, discreteMarginal_real, jointWeight,
    ENNReal.toReal_mul, discrete_coord ho]
  norm_num
  ring

lemma tvMessage_le_one (m : Message) : tvMessage m ≤ 1 := by
  have hb (i : Spin) : |m.1 i-1| ≤ 2 := abs_le.mpr ⟨by linarith [coordinate_nonneg m i],
    by linarith [coordinate_le_three m i]⟩
  dsimp [tvMessage, avg]
  linarith [hb 0, hb 1, hb 2]

lemma integrable_tv_discrete {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : Spin → PMF α) :
    Integrable (fun o ↦ tvMessage (discreteMessage p o)) (discreteMarginal p).toMeasure := by
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun a ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (tvMessage_nonneg _)]
    exact tvMessage_le_one _)

lemma advantage_eq_integral (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) (ℓ : ℕ) :
    advantage lam hlam offspring ℓ =
      ∫ m, tvMessage m ∂(discreteProbability (observationLaw lam hlam offspring ℓ)).toMeasure := by
  have hi : Integrable (fun o ↦ tvMessage (discreteMessage (observationLaw lam hlam offspring ℓ) o))
      (discreteMarginal (observationLaw lam hlam offspring ℓ)).toMeasure :=
    integrable_tv_discrete (observationLaw lam hlam offspring ℓ)
  rw [integral_discreteProbability _ continuous_tvMessage.measurable, PMF.integral_eq_tsum _ _ hi]
  unfold advantage
  apply tsum_congr
  intro o
  rw [main_marginal_eq, discreteMarginal_real]
  simp only [smul_eq_mul]
  by_cases ho : discreteWeight (observationLaw lam hlam offspring ℓ) o = 0
  · simp only [ho, zero_mul]
  · simp only [main_posterior_eq lam hlam offspring ℓ o ho, tvMessage_formula]

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


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Experiment.advantage_eq_integral := @_root_.OAI.ThreeState.TreeClauses.Experiment.advantage_eq_integral
