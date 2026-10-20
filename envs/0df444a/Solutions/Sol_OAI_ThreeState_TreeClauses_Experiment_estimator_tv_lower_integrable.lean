-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Experiment.estimator_tv_lower_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:41:48.211444+00:00
-- url     : https://prove2.me/submissions/086afa81-1eaa-4bb7-89f5-759b15e9448f

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/CountableStatistics.lean:L95-L139
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Experiment.estimator_tv_lower_integrable. The node keeps its source
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
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularStatistics
import Definitions.Def_OAI_Probability_ThreeStateClauses_InformationLoss
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularReconstruction
import Definitions.Def_OAI_Probability_ThreeStateClauses_ObservedMixtures
import Definitions.Def_OAI_Probability_ThreeStateClauses_OffspringLaws

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

lemma tvMessage_le_one (m : Message) : tvMessage m ≤ 1 := by
  have hb (i : Spin) : |m.1 i-1| ≤ 2 := abs_le.mpr ⟨by linarith [coordinate_nonneg m i],
    by linarith [coordinate_le_three m i]⟩
  dsimp [tvMessage, avg]
  linarith [hb 0, hb 1, hb 2]

end ThreeState.TreeClauses.Experiment

end

end OAI

-- ---- from OAI.Probability.ThreeStateClauses.InformationLoss ----
namespace OAI

/-! Information Loss. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {α β γ : Type}

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

lemma coord_center_abs_le_two (m : Message) (i : Spin) : |m.1 i-1| ≤ 2 :=
  abs_le.mpr ⟨by linarith [coordinate_nonneg m i], by linarith [coordinate_le_three m i]⟩

variable {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma coord_sq_le_tv (m : Message) (i : Spin) : (m.1 i-1)^2 ≤ 12*tvMessage m := by
  have h := mul_le_mul_of_nonneg_left (coord_center_abs_le_two m i) (abs_nonneg (m.1 i-1))
  rw [← sq, sq_abs] at h
  have hs : |m.1 i-1| ≤ ∑ j : Spin, |m.1 j-1| :=
    Finset.single_le_sum (f := fun j : Spin ↦ |m.1 j-1|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)
  simp only [Fin.sum_univ_three] at hs
  dsimp [tvMessage, avg]
  linarith

omit [Countable α] [MeasurableSingletonClass α] in
lemma integral_scaled_square (μ : Measure α) {v f : α → ℝ} (r : ℝ)
    (hv : Integrable (fun a ↦ v a^2) μ) (hf : Integrable (fun a ↦ f a^2) μ)
    (hc : Integrable (fun a ↦ v a*f a) μ) :
    (∫ a, (v a-r*f a)^2 ∂μ) = (∫ a, v a^2 ∂μ)-2*r*(∫ a, v a*f a ∂μ)+r^2*(∫ a, f a^2 ∂μ) := by
  have he (a : α) : (v a-r*f a)^2 = (v a^2-(2*r)*(v a*f a))+r^2*f a^2 := by ring
  simp_rw [he]
  rw [integral_add (f := fun a ↦ v a^2-(2*r)*(v a*f a)) (g := fun a ↦ r^2*f a^2)
    (hv.sub (hc.const_mul (2*r))) (hf.const_mul (r^2))]
  rw [integral_sub hv (hc.const_mul (2*r))]
  rw [integral_const_mul, integral_const_mul]

end ThreeState.TreeClauses.Experiment

end

end OAI

-- ---- from OAI.Probability.ThreeStateClauses.CountableStatistics ----
namespace OAI

/-! Countable Statistics. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

lemma pmf_measure_sum_dirac (p : PMF α) :
    p.toMeasure = Measure.sum (fun a ↦ p a • Measure.dirac a) := by
  simpa only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] using
    (Measure.sum_smul_dirac p.toMeasure).symm

lemma pmf_integrable_iff (p : PMF α) (f : α → ℝ) :
    Integrable f p.toMeasure ↔ Summable (fun a ↦ (p a).toReal*|f a|) := by
  rw [pmf_measure_sum_dirac, integrable_sum_dirac_iff (fun a ↦ p.apply_ne_top a)]
  rfl

omit [Countable β] [MeasurableSingletonClass β] in
lemma pmf_integrable_bind (p : PMF α) (K : α → PMF β) {f : β → ℝ}
    (hf : ∀ a, Integrable f (K a).toMeasure)
    (hn : Integrable (fun a ↦ ∫ b, |f b| ∂(K a).toMeasure) p.toMeasure) :
    Integrable f (p.bind K).toMeasure := by
  rw [pmf_measure_bind]
  apply integrable_sum_measure (fun a ↦ (hf a).smul_measure (p.apply_ne_top a))
  have h := (pmf_integrable_iff p _).mp hn
  simpa only [integral_smul_measure, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ ↦ abs_nonneg _))] using h

omit [Countable α] [MeasurableSingletonClass α] in
lemma pmf_integrable_bind_finite {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (p : PMF ι) (K : ι → PMF α) {f : α → ℝ}
    (hf : ∀ i, Integrable f (K i).toMeasure) : Integrable f (p.bind K).toMeasure :=
  pmf_integrable_bind p K hf Integrable.of_finite

lemma pmf_integrable_of_square (p : PMF α) {f : α → ℝ}
    (hf : Integrable (fun a ↦ f a^2) p.toMeasure) : Integrable f p.toMeasure := by
  apply ((integrable_const (1:ℝ)).add hf).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun a ↦ by
    simp only [Real.norm_eq_abs, Pi.add_apply]
    nlinarith [sq_nonneg (|f a|-1), sq_abs (f a)])

lemma discrete_bayes_integral_integrable (p : Spin → PMF α) (i : Spin) {f : α → ℝ}
    (hf : Integrable f (discreteMarginal p).toMeasure) (hi : Integrable f (p i).toMeasure) :
    (∫ a, (discreteMessage p a).1 i*f a ∂(discreteMarginal p).toMeasure) =
      ∫ a, f a ∂(p i).toMeasure := by
  have hl := hf.bdd_mul (measurable_of_countable (fun a ↦ (discreteMessage p a).1 i)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a ↦ show ‖(discreteMessage p a).1 i‖ ≤ (3:ℝ) by
      rw [Real.norm_eq_abs, abs_of_nonneg (coordinate_nonneg _ _)]; exact coordinate_le_three _ _))
  rw [PMF.integral_eq_tsum _ _ hl, PMF.integral_eq_tsum _ _ hi]
  apply tsum_congr
  intro a
  simp only [smul_eq_mul, discreteMarginal_real, ← mul_assoc, discrete_bayes]

lemma estimator_tv_lower_integrable (p : Spin → PMF α) {f : α → ℝ} {C : ℝ}
    (hf : ∀ i, Integrable (fun a ↦ f a^2) (p i).toMeasure) (hC : 0 < C)
    (hzero : (∫ a, f a ∂(discreteMarginal p).toMeasure) = 0)
    (hroot : (∫ a, f a ∂(p 0).toMeasure) = 2)
    (hsecond : (∫ a, f a^2 ∂(discreteMarginal p).toMeasure) ≤ C) :
    1/(3*C) ≤ ∫ m, tvMessage m ∂(discreteProbability p).toMeasure := by
  let v : α → ℝ := fun a ↦ (discreteMessage p a).1 0-1
  have hv (a : α) : |v a| ≤ 2 := coord_center_abs_le_two _ _
  have hf₂ : Integrable (fun a ↦ f a^2) (discreteMarginal p).toMeasure :=
    pmf_integrable_bind_finite _ _ hf
  have hf₁ := pmf_integrable_of_square _ hf₂
  have hv₂ := pmf_bounded_integrable (discreteMarginal p) (fun a ↦ show |v a^2| ≤ (2:ℝ)^2 by
    rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [hv a, abs_nonneg (v a), sq_abs (v a)])
  have hvf := hf₁.bdd_mul (measurable_of_countable v).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun a ↦ show ‖v a‖ ≤ (2:ℝ) from hv a))
  have hcross : (∫ a, v a*f a ∂(discreteMarginal p).toMeasure) = 2 := by
    have he (a : α) : v a*f a = (discreteMessage p a).1 0*f a-f a := by dsimp [v]; ring
    simp_rw [he]
    rw [integral_sub (hf₁.bdd_mul (measurable_of_countable _).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun a ↦ show ‖(discreteMessage p a).1 0‖ ≤ (3:ℝ) by
        rw [Real.norm_eq_abs, abs_of_nonneg (coordinate_nonneg _ _)]; exact coordinate_le_three _ _))) hf₁,
      discrete_bayes_integral_integrable p 0 hf₁ (pmf_integrable_of_square _ (hf 0)), hroot, hzero, sub_zero]
  let r := 2/C
  have hr : r*C = 2 := div_mul_cancel₀ 2 hC.ne'
  have h := MeasureTheory.integral_nonneg (μ := (discreteMarginal p).toMeasure)
    (f := fun a ↦ (v a-r*f a)^2) (fun _ ↦ sq_nonneg _)
  rw [integral_scaled_square _ r hv₂ hf₂ hvf, hcross] at h
  have hb := mul_le_mul_of_nonneg_left hsecond (sq_nonneg r)
  have hr2 : r^2*C = 2*r := by
    have hh := congrArg (fun x : ℝ ↦ r*x) hr
    nlinarith only [hh]
  have hD : 4 ≤ C*(∫ a, v a^2 ∂(discreteMarginal p).toMeasure) := by
    have hs : 2*r ≤ ∫ a, v a^2 ∂(discreteMarginal p).toMeasure := by
      nlinarith only [h, hb, hr2]
    have hh := mul_le_mul_of_nonneg_left hs hC.le
    nlinarith only [hh, hr]
  have hT := integral_mono hv₂ (pmf_bounded_integrable (discreteMarginal p)
    (fun a ↦ show |12*tvMessage (discreteMessage p a)| ≤ 12 by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 12), abs_of_nonneg (tvMessage_nonneg _)];
      nlinarith [tvMessage_le_one (discreteMessage p a)]))
    (fun a ↦ coord_sq_le_tv (discreteMessage p a) 0)
  rw [integral_const_mul, ← integral_discreteProbability p continuous_tvMessage.measurable] at hT
  apply (div_le_iff₀ (by positivity : 0 < 3*C)).2
  have hh := mul_le_mul_of_nonneg_left hT hC.le
  nlinarith only [hD, hh]

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

section Sigma
variable {β : ℕ → Type*} [∀ n, Countable (β n)] [∀ n, MeasurableSpace (β n)]
  [∀ n, MeasurableSingletonClass (β n)]

end Sigma
end ThreeState.TreeClauses.Experiment

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Experiment
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators
open ThreeState.TreeClauses.Radial


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Experiment.estimator_tv_lower_integrable := @_root_.OAI.ThreeState.TreeClauses.Experiment.estimator_tv_lower_integrable
