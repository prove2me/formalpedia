-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Tree.poisson_reconstructs_above_KS
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:55:16.792713+00:00
-- url     : https://prove2.me/submissions/06d1e332-c896-4e9f-8a12-f7f0e377dd40

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/PoissonReconstruction.lean:L192-L197
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ThreeState.TreeClauses.Tree.poisson_reconstructs_above_KS.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_poisson_reconstructs_above_KS) verbatim and is proved by it.
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
import Definitions.Def_OAI_Probability_ThreeStateClauses_PoissonReconstruction
import Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_advantage_eq_integral
import Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_discrete_degradation_centered
import Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_estimator_tv_lower_integrable
import Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_orderedLaw_forget
import Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_poissonStatistic_mean
import Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_poissonStatistic_second
import Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_poissonStatistic_square_integrable

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

lemma integral_avg_measure {X : Type*} [MeasurableSpace X] {ν : Measure X} {f : X → Vec}
    (hf : ∀ i, Integrable (fun x ↦ f x i) ν) :
    (∫ x, avg (f x) ∂ν) = avg (fun i ↦ ∫ x, f x i ∂ν) := by
  simp only [avg, integral_div]
  rw [integral_add (f := fun x ↦ f x 0+f x 1) (g := fun x ↦ f x 2) ((hf 0).add (hf 1)) (hf 2),
    integral_add (f := fun x ↦ f x 0) (g := fun x ↦ f x 1) (hf 0) (hf 1)]

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

lemma integral_pmf_map (p : PMF α) (T : α → β) (f : β → ℝ) :
    (∫ b, f b ∂(p.map T).toMeasure) = ∫ a, f (T a) ∂p.toMeasure := by
  rw [← PMF.toMeasure_map T p (measurable_of_countable T)]
  exact integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable

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

lemma kernelJoint_fst (p : PMF α) (K : α → PMF β) :
    (kernelJoint p K).map Prod.fst = p := by
  simp only [kernelJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have h (a : α) : ((K a).map (fun _ ↦ a)) = PMF.pure a := PMF.map_const _ _
  simp only [h, PMF.bind_pure]

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

lemma integral_kernelJoint_fst (p : PMF α) (K : α → PMF β) (f : α → ℝ) :
    (∫ z, f z.1 ∂(kernelJoint p K).toMeasure) = ∫ a, f a ∂p.toMeasure := by
  rw [← integral_pmf_map, kernelJoint_fst]

lemma integral_kernelJoint_snd (p : PMF α) (K : α → PMF β) (f : β → ℝ) :
    (∫ z, f z.2 ∂(kernelJoint p K).toMeasure) = ∫ b, f b ∂(p.bind K).toMeasure := by
  rw [← integral_pmf_map, kernelJoint_snd]

end Measures
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

lemma advantage_nonneg (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) (ℓ : ℕ) :
    0 ≤ advantage lam hlam offspring ℓ := by
  rw [advantage_eq_integral]
  exact MeasureTheory.integral_nonneg tvMessage_nonneg

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

lemma multisetKernel_iid (p : PMF α) (K : α → PMF β) (n : ℕ) :
    ((iidList p n).map (fun xs : List α ↦ (xs : Multiset α))).bind (multisetKernel K) =
      (iidList (p.bind K) n).map (fun xs : List β ↦ (xs : Multiset β)) := by
  induction n with
  | zero => simp [iidList, PMF.pure_map]
  | succ n ih =>
    simp only [iidList, PMF.map_bind, PMF.map_comp, PMF.bind_bind, PMF.bind_map]
    congr 1
    funext a
    simp only [Function.comp_def, ← Multiset.cons_coe, multisetKernel_cons]
    rw [PMF.bind_comm (iidList p n) (K a)]
    congr 1
    funext b
    rw [← PMF.map_bind]
    have hi := ih
    rw [PMF.bind_map] at hi
    dsimp only [Function.comp_def] at hi
    rw [hi, PMF.map_comp]
    rfl

lemma observationLaw_succ (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (i : Spin) :
    observationLaw lam hlam offspring (ℓ+1) i = offspring.bind (fun n ↦
      (iidList ((channel lam hlam i).bind (observationLaw lam hlam offspring ℓ)) n).map
        (fun xs : List (Observation ℓ) ↦ (xs : Multiset (Observation ℓ)))) := by
  rw [observationLaw]
  congr 1
  funext n
  exact PMF.map_id _

lemma observationLaw_degrades (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (i : Spin) :
    (observationLaw lam hlam offspring ℓ i).bind (observationExpansion lam hlam offspring ℓ) =
      observationLaw lam hlam offspring (ℓ+1) i := by
  induction ℓ generalizing i with
  | zero => exact PMF.pure_bind _ _
  | succ ℓ ih =>
    rw [observationLaw_succ, observationLaw_succ]
    change ((offspring.bind (fun n ↦ (iidList ((channel lam hlam i).bind (observationLaw lam hlam offspring ℓ)) n).map
      (fun xs : List (Observation ℓ) ↦ (xs : Multiset (Observation ℓ))))).bind
      (multisetKernel (observationExpansion lam hlam offspring ℓ))) = _
    rw [PMF.bind_bind]
    congr 1
    funext n
    rw [multisetKernel_iid]
    congr 2
    rw [PMF.bind_bind]
    congr 1
    funext j
    exact ih j

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

lemma discrete_degradation_abs (p : Spin → PMF α) (K : α → PMF β) (i : Spin) :
    (∫ b, |(discreteMessage (fun j ↦ (p j).bind K) b).1 i-1|
      ∂(discreteMarginal (fun j ↦ (p j).bind K)).toMeasure) ≤
    ∫ a, |(discreteMessage p a).1 i-1| ∂(discreteMarginal p).toMeasure := by
  let q := fun j ↦ (p j).bind K
  let g : β → ℝ := fun b ↦ if 0 ≤ (discreteMessage q b).1 i-1 then 1 else -1
  have hg (b : β) : |g b| ≤ 1 := by dsimp [g]; split_ifs <;> norm_num
  have he (b : β) : ((discreteMessage q b).1 i-1)*g b = |(discreteMessage q b).1 i-1| := by
    dsimp [g]; split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have hb (z : α × β) : |((discreteMessage p z.1).1 i-1)*g z.2| ≤ 2 := by
    rw [abs_mul]
    exact (mul_le_mul (coord_center_abs_le_two _ _) (hg _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hi := discrete_degradation_centered p K i hg
  have hid (z : α × β) : ((discreteMessage p z.1).1 i-(discreteMessage q z.2).1 i)*g z.2 =
      ((discreteMessage p z.1).1 i-1)*g z.2-|(discreteMessage q z.2).1 i-1| := by
    rw [← he]; ring
  change (∫ z : α × β, ((discreteMessage p z.1).1 i-(discreteMessage q z.2).1 i)*g z.2 ∂_) = 0 at hi
  simp_rw [hid] at hi
  rw [integral_sub (pmf_bounded_integrable _ hb)
    (pmf_bounded_integrable _ (fun z : α × β ↦ by simpa using coord_center_abs_le_two (discreteMessage q z.2) i))] at hi
  have hle : (∫ z, ((discreteMessage p z.1).1 i-1)*g z.2 ∂(kernelJoint (discreteMarginal p) K).toMeasure) ≤
      ∫ z, |(discreteMessage p z.1).1 i-1| ∂(kernelJoint (discreteMarginal p) K).toMeasure :=
    integral_mono (μ := (kernelJoint (discreteMarginal p) K).toMeasure)
    (pmf_bounded_integrable _ hb)
    (pmf_bounded_integrable _ (fun z : α × β ↦ by simpa using coord_center_abs_le_two (discreteMessage p z.1) i))
    (fun z : α × β ↦ (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hg _)))
  rw [integral_kernelJoint_fst (f := fun a ↦ |(discreteMessage p a).1 i-1|)] at hle
  rw [integral_kernelJoint_snd (f := fun b ↦ |(discreteMessage q b).1 i-1|), ← discreteMarginal_bind] at hi
  change _ - (∫ b, |(discreteMessage q b).1 i-1| ∂(discreteMarginal q).toMeasure) = 0 at hi
  linarith

lemma discrete_degradation_tv (p : Spin → PMF α) (K : α → PMF β) :
    (∫ m, tvMessage m ∂(discreteProbability (fun i ↦ (p i).bind K)).toMeasure) ≤
      ∫ m, tvMessage m ∂(discreteProbability p).toMeasure := by
  rw [integral_discreteProbability _ continuous_tvMessage.measurable,
    integral_discreteProbability _ continuous_tvMessage.measurable]
  unfold tvMessage
  rw [integral_div, integral_div, integral_avg_measure, integral_avg_measure]
  · exact div_le_div_of_nonneg_right (by
      dsimp [avg]
      linarith [discrete_degradation_abs p K 0, discrete_degradation_abs p K 1,
        discrete_degradation_abs p K 2]) (by norm_num)
  all_goals intro i; exact pmf_bounded_integrable _ (fun a ↦ by simpa using coord_center_abs_le_two _ i)

lemma advantage_antitone (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) :
    Antitone (advantage lam hlam offspring) := by
  apply antitone_nat_of_succ_le
  intro ℓ
  simp only [advantage_eq_integral]
  have h := discrete_degradation_tv (observationLaw lam hlam offspring ℓ)
    (observationExpansion lam hlam offspring ℓ)
  simpa only [observationLaw_degrades] using h

lemma advantage_tendsto (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) :
    Tendsto (advantage lam hlam offspring) atTop (𝓝 (⨅ ℓ, advantage lam hlam offspring ℓ)) :=
  tendsto_atTop_ciInf (advantage_antitone lam hlam offspring)
    ⟨0, by rintro _ ⟨ℓ,rfl⟩; exact advantage_nonneg lam hlam offspring ℓ⟩

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

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

lemma integral_pmf_tsum (p : PMF α) (f : α → ℝ) :
    (∫ a, f a ∂p.toMeasure) = ∑' a, (p a).toReal*f a := by
  rw [pmf_measure_sum_dirac, integral_sum_dirac (fun a ↦ p.apply_ne_top a)]
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

omit [Countable β] [MeasurableSingletonClass β] in
lemma integral_pmf_bind_integrable (p : PMF α) (K : α → PMF β) {f : β → ℝ}
    (hf : Integrable f (p.bind K).toMeasure) :
    (∫ b, f b ∂(p.bind K).toMeasure) = ∫ a, (∫ b, f b ∂(K a).toMeasure) ∂p.toMeasure := by
  rw [pmf_measure_bind] at hf ⊢
  rw [integral_sum_measure hf, integral_pmf_tsum]
  simp only [integral_smul_measure, smul_eq_mul]

omit [Countable α] [MeasurableSingletonClass α] in
lemma pmf_integrable_bind_finite {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (p : PMF ι) (K : ι → PMF α) {f : α → ℝ}
    (hf : ∀ i, Integrable f (K i).toMeasure) : Integrable f (p.bind K).toMeasure :=
  pmf_integrable_bind p K hf Integrable.of_finite

lemma pmf_integrable_map_iff (p : PMF α) (g : α → β) (f : β → ℝ) :
    Integrable f (p.map g).toMeasure ↔ Integrable (fun a ↦ f (g a)) p.toMeasure := by
  rw [← PMF.toMeasure_map g p (measurable_of_countable g)]
  exact integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable

lemma pmf_integrable_of_square (p : PMF α) {f : α → ℝ}
    (hf : Integrable (fun a ↦ f a^2) p.toMeasure) : Integrable f p.toMeasure := by
  apply ((integrable_const (1:ℝ)).add hf).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun a ↦ by
    simp only [Real.norm_eq_abs, Pi.add_apply]
    nlinarith [sq_nonneg (|f a|-1), sq_abs (f a)])

omit [Countable α] [MeasurableSingletonClass α] in
lemma integral_discreteMarginal_integrable (p : Spin → PMF α) {f : α → ℝ}
    (hf : ∀ i, Integrable f (p i).toMeasure) :
    (∫ a, f a ∂(discreteMarginal p).toMeasure) =
      ((∫ a, f a ∂(p 0).toMeasure)+(∫ a, f a ∂(p 1).toMeasure)+(∫ a, f a ∂(p 2).toMeasure))/3 := by
  rw [discreteMarginal, integral_pmf_bind_integrable _ _ (pmf_integrable_bind_finite _ _ hf), PMF.integral_eq_sum]
  simp only [Fin.sum_univ_three, uniformSpin_apply, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

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

-- ---- from OAI.Probability.ThreeStateClauses.PoissonReconstruction ----
namespace OAI

/-! Poisson Reconstruction. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability

lemma observedStatistic_forget (d lam : ℝ) (ℓ : ℕ) (v : OrderedObservation ℓ) :
    observedStatistic d lam ℓ (forgetOrdered ℓ v) = orderedStatistic d lam ℓ v := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rcases v with ⟨n,v⟩
    simp only [forgetOrdered, observedStatistic, orderedStatistic]
    congr 1
    simp only [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, Function.comp_def, ih, List.sum_ofFn]

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability

lemma poissonKSConstant_pos {d lam : ℝ} (hKS : 1 < d*lam^2) : 0 < poissonKSConstant d lam := by
  unfold poissonKSConstant; positivity

lemma poisson_estimator_advantage (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (d:ℝ)*lam^2) (ℓ : ℕ) :
    1/(3*poissonKSConstant d lam) ≤ advantage lam hlam (poissonPMF d) ℓ := by
  have hd : (d:ℝ) ≠ 0 := by intro h; norm_num [h] at hKS
  have hl : lam ≠ 0 := by intro h; norm_num [h] at hKS
  let p := observationLaw lam hlam (poissonPMF d) ℓ
  let f := observedStatistic d lam ℓ
  have hInt (i : Spin) : Integrable (fun o ↦ f o^2) (p i).toMeasure := by
    dsimp [p, f]
    rw [← orderedLaw_forget _ lam hlam ℓ i, pmf_integrable_map_iff]
    simpa only [observedStatistic_forget] using poissonStatistic_square_integrable d lam hlam ℓ i
  have hmean (i : Spin) : (∫ o, f o ∂(p i).toMeasure) = spinScore i := by
    dsimp [p, f]
    rw [← orderedLaw_forget _ lam hlam ℓ i, integral_pmf_map]
    simp_rw [observedStatistic_forget]
    exact poissonStatistic_mean d hd lam hlam hl ℓ i
  have hsecond (i : Spin) : (∫ o, f o^2 ∂(p i).toMeasure) ≤ poissonKSConstant d lam := by
    dsimp [p, f]
    rw [← orderedLaw_forget _ lam hlam ℓ i, integral_pmf_map]
    simp_rw [observedStatistic_forget]
    exact poissonStatistic_second d lam hlam hKS ℓ i
  rw [advantage_eq_integral]
  apply estimator_tv_lower_integrable (p := p) hInt (poissonKSConstant_pos hKS)
  · rw [integral_discreteMarginal_integrable p (fun i ↦ pmf_integrable_of_square _ (hInt i)),
      hmean 0, hmean 1, hmean 2]
    norm_num [spinScore, show (1:Spin) ≠ 0 by decide, show (2:Spin) ≠ 0 by decide]
  · exact hmean 0
  · rw [integral_discreteMarginal_integrable p hInt]
    linarith [hsecond 0, hsecond 1, hsecond 2]

theorem poisson_reconstructs_above_KS (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (d:ℝ)*lam^2) : Reconstructs lam hlam (poissonPMF d) := by
  refine ⟨⨅ ℓ, advantage lam hlam (poissonPMF d) ℓ, ?_, advantage_tendsto _ _ _⟩
  have he : 1/(3*poissonKSConstant d lam) ≤ ⨅ ℓ, advantage lam hlam (poissonPMF d) ℓ := by
    exact le_ciInf (fun ℓ ↦ poisson_estimator_advantage d lam hlam hKS ℓ)
  exact (div_pos (by norm_num) (mul_pos (by norm_num) (poissonKSConstant_pos hKS))).trans_le he

end ThreeState.TreeClauses.Tree

end

end OAI

-- ---- mission target ----
open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal
open Filter
open scoped Topology
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability

namespace OAI
namespace ThreeState.TreeClauses.Tree
theorem _root_.solution (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (d:ℝ)*lam^2) : Reconstructs lam hlam (poissonPMF d) := by
  first
    | exact OAI.ThreeState.TreeClauses.Tree.poisson_reconstructs_above_KS d lam hlam hKS
    | exact OAI.ThreeState.TreeClauses.Tree.poisson_reconstructs_above_KS
    | (apply OAI.ThreeState.TreeClauses.Tree.poisson_reconstructs_above_KS <;> assumption)
    | (intros; apply OAI.ThreeState.TreeClauses.Tree.poisson_reconstructs_above_KS <;> assumption)
end ThreeState.TreeClauses.Tree
end OAI
