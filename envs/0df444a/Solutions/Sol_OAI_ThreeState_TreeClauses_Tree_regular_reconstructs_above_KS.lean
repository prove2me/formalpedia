-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Tree.regular_reconstructs_above_KS
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:53:20.152547+00:00
-- url     : https://prove2.me/submissions/c8a3c266-5acb-45f0-afee-5b43757e3fa1

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/RegularReconstruction.lean:L103-L108
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ThreeState.TreeClauses.Tree.regular_reconstructs_above_KS.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_regular_reconstructs_above_KS) verbatim and is proved by it.
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
import Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_advantage_eq_integral
import Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_discrete_degradation_centered
import Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_estimator_tv_lower
import Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_integral_pmf_bind
import Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_integral_weighted_sq_sum
import Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_observedRegularStatistic_bound
import Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_regularLaw_forget
import Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_regularStatistic_mean

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

lemma integral_pmf_map (p : PMF α) (T : α → β) (f : β → ℝ) :
    (∫ b, f b ∂(p.map T).toMeasure) = ∫ a, f (T a) ∂p.toMeasure := by
  rw [← PMF.toMeasure_map T p (measurable_of_countable T)]
  exact integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable

end ThreeState.TreeClauses.Experiment

end

end OAI

-- ---- from OAI.Probability.ThreeStateClauses.Products ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Products. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment

variable {α β : Type*}

lemma productPMF_measure [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {n : ℕ} (p : Fin n → PMF α) :
    (productPMF p).toMeasure = Measure.pi (fun j ↦ (p j).toMeasure) := by
  have h : productPMF p = (Measure.pi (fun j ↦ (p j).toMeasure)).toPMF := by
    apply PMF.ext
    intro v
    simp [productPMF_apply, Measure.toPMF_apply, Measure.pi_singleton, PMF.toMeasure_apply_singleton]
  rw [h, Measure.toPMF_toMeasure]

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

-- ---- from OAI.Probability.ThreeStateClauses.RegularCritical ----
namespace OAI

/-! Regular Critical. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Tree
-- [generator] trimmed: open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

lemma channelWeight_alt (lam : ℝ) (i j : Spin) :
    channelWeight lam i j = lam*(if i = j then 1 else 0)+(1-lam)/3 := by
  unfold channelWeight
  split_ifs <;> ring

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ThreeState.TreeClauses.Tree
-- [generator] trimmed: open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Tree

end

end OAI

-- ---- from OAI.Probability.ThreeStateClauses.RegularStatistics ----
namespace OAI

/-! Regular Statistics. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma finite_abs_bound (f : α → ℝ) : ∃ C : ℝ, ∀ a, |f a| ≤ C := by
  obtain ⟨C,hC⟩ := (Set.finite_range (fun a ↦ |f a|)).bddAbove
  exact ⟨C, fun a ↦ hC ⟨a,rfl⟩⟩

lemma integral_pmf_bind_finite (p : PMF α) (K : α → PMF β) (f : β → ℝ) :
    (∫ b, f b ∂(p.bind K).toMeasure) = ∫ a, (∫ b, f b ∂(K a).toMeasure) ∂p.toMeasure := by
  obtain ⟨C,hC⟩ := finite_abs_bound f
  exact integral_pmf_bind p K hC

lemma integral_product_sq_sum (p : PMF α) (f : α → ℝ) (n : ℕ) :
    (∫ v : Fin n → α, (∑ j, f (v j))^2 ∂(productPMF (fun _ ↦ p)).toMeasure) =
      (n:ℝ)*(∫ a, f a^2 ∂p.toMeasure)+((n:ℝ)^2-n)*(∫ a, f a ∂p.toMeasure)^2 := by
  rw [productPMF_measure]
  simpa [weightProduct] using integral_weighted_sq_sum (ι := Fin n) (a := fun _ : α ↦ (1:ℝ))
    (u := f) (integrable_const 1) Integrable.of_finite Integrable.of_finite (by simp)

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

lemma spinScore_square (i : Spin) : spinScore i^2 ≤ 4 := by
  unfold spinScore; split_ifs <;> norm_num

lemma channel_spinScore (lam : ℝ) (hlam : Admissible lam) (i : Spin) :
    (∫ j, spinScore j ∂(channel lam hlam i).toMeasure) = lam*spinScore i := by
  rw [PMF.integral_eq_sum]
  have he (j : Spin) : (channel lam hlam i j).toReal = channelWeight lam i j :=
    ENNReal.toReal_ofReal (channelWeight_nonneg hlam i j)
  simp only [smul_eq_mul, he]
  simp_rw [channelWeight_alt, add_mul, Finset.sum_add_distrib]
  have hs : ∑ j : Spin, spinScore j = 0 := by
    norm_num [Fin.sum_univ_three, spinScore, show (1:Spin) ≠ 0 by decide, show (2:Spin) ≠ 0 by decide]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, ← Finset.mul_sum, hs, mul_zero, add_zero]

lemma observedRegularStatistic_forget (b : ℕ) (lam : ℝ) (ℓ : ℕ)
    (v : RegularObservation b ℓ) :
    observedRegularStatistic b lam ℓ (forgetRegular b ℓ v) = regularStatistic b lam ℓ v := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    simp only [forgetRegular, observedRegularStatistic, Multiset.coe_card, List.length_ofFn, ite_true, regularStatistic]
    congr 1
    simp only [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, Function.comp_def, ih, List.sum_ofFn]

end ThreeState.TreeClauses.Tree

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

lemma integral_discreteMarginal (p : Spin → PMF α) {f : α → ℝ} {B : ℝ} (hB : ∀ a, |f a| ≤ B) :
    (∫ a, f a ∂(discreteMarginal p).toMeasure) =
      ((∫ a, f a ∂(p 0).toMeasure)+(∫ a, f a ∂(p 1).toMeasure)+(∫ a, f a ∂(p 2).toMeasure))/3 := by
  rw [discreteMarginal, integral_pmf_bind _ _ hB, PMF.integral_eq_sum]
  simp only [Fin.sum_univ_three, uniformSpin_apply, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

end ThreeState.TreeClauses.Experiment

end

end OAI

-- ---- from OAI.Probability.ThreeStateClauses.RegularReconstruction ----
namespace OAI

/-! Regular Reconstruction. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

lemma ksConstant_pos {b : ℕ} {lam : ℝ} (hKS : 1 < (b:ℝ)*lam^2) : 0 < ksConstant b lam := by
  unfold ksConstant; positivity

lemma ksConstant_ge_four {b : ℕ} {lam : ℝ} (hKS : 1 < (b:ℝ)*lam^2) : 4 ≤ ksConstant b lam := by
  rw [ksConstant, le_div_iff₀ (by linarith)]
  linarith

lemma ksConstant_identity {b : ℕ} {lam : ℝ} (hKS : 1 < (b:ℝ)*lam^2) :
    ksConstant b lam*((b:ℝ)*lam^2-1) = 4*((b:ℝ)*lam^2) := by
  rw [ksConstant, div_mul_cancel₀ _ (by linarith)]

lemma regularStatistic_second (b : ℕ) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (b:ℝ)*lam^2) (ℓ : ℕ) (i : Spin) :
    (∫ v, regularStatistic b lam ℓ v^2 ∂(regularLaw b lam hlam ℓ i).toMeasure) ≤ ksConstant b lam := by
  have hb : 0 < b := by
    by_contra h
    have hb0 : b = 0 := by omega
    norm_num [hb0] at hKS
  have hb' : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hl : lam ≠ 0 := by intro h; norm_num [h] at hKS
  have hden : 0 < ((b:ℝ)*lam)^2 := sq_pos_of_ne_zero (mul_ne_zero (ne_of_gt hb') hl)
  have hC := ksConstant_pos hKS
  induction ℓ generalizing i with
  | zero =>
    change (∫ v : Spin, spinScore v^2 ∂(PMF.pure i).toMeasure) ≤ _
    rw [PMF.toMeasure_pure, integral_dirac]
    exact (spinScore_square i).trans (ksConstant_ge_four hKS)
  | succ ℓ ih =>
    have hmean : (∫ v, regularStatistic b lam ℓ v
        ∂((channel lam hlam i).bind (regularLaw b lam hlam ℓ)).toMeasure) = lam*spinScore i := by
      rw [integral_pmf_bind_finite]
      simp_rw [regularStatistic_mean b hb lam hlam hl ℓ]
      exact channel_spinScore lam hlam i
    have hsecond : (∫ v, regularStatistic b lam ℓ v^2
        ∂((channel lam hlam i).bind (regularLaw b lam hlam ℓ)).toMeasure) ≤ ksConstant b lam := by
      rw [integral_pmf_bind_finite]
      exact (integral_mono Integrable.of_finite (integrable_const _) (ih)).trans_eq (by simp)
    change (∫ v : Fin b → RegularObservation b ℓ,
      ((∑ j, regularStatistic b lam ℓ (v j))/((b:ℝ)*lam))^2
      ∂(productPMF (fun _ ↦ (channel lam hlam i).bind (regularLaw b lam hlam ℓ))).toMeasure) ≤ _
    simp_rw [div_pow]
    rw [integral_div, integral_product_sq_sum, hmean]
    apply (div_le_iff₀ hden).2
    have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hb
    have hn : 0 ≤ (b:ℝ)^2-b := by nlinarith
    have hs := mul_le_mul_of_nonneg_left (spinScore_square i) (sq_nonneg lam)
    have hp := mul_le_mul_of_nonneg_left hs hn
    have hi := congrArg (fun x : ℝ ↦ x*(b:ℝ)) (ksConstant_identity hKS)
    have hm := mul_le_mul_of_nonneg_left hsecond hb'.le
    nlinarith [mul_nonneg hb'.le (sq_nonneg lam)]

lemma regular_estimator_advantage (b : ℕ) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (b:ℝ)*lam^2) (ℓ : ℕ) :
    1/(3*ksConstant b lam) ≤ advantage lam hlam (PMF.pure b) ℓ := by
  have hb : 0 < b := by
    by_contra h
    have hb0 : b = 0 := by omega
    norm_num [hb0] at hKS
  have hl : lam ≠ 0 := by intro h; norm_num [h] at hKS
  let p := observationLaw lam hlam (PMF.pure b) ℓ
  let f := observedRegularStatistic b lam ℓ
  obtain ⟨B,hB0,hB⟩ := observedRegularStatistic_bound b lam ℓ
  have hmean (i : Spin) : (∫ o, f o ∂(p i).toMeasure) = spinScore i := by
    dsimp [p, f]
    rw [← regularLaw_forget b lam hlam ℓ i, integral_pmf_map]
    simp_rw [observedRegularStatistic_forget]
    exact regularStatistic_mean b hb lam hlam hl ℓ i
  have hsecond (i : Spin) : (∫ o, f o^2 ∂(p i).toMeasure) ≤ ksConstant b lam := by
    dsimp [p, f]
    rw [← regularLaw_forget b lam hlam ℓ i, integral_pmf_map]
    simp_rw [observedRegularStatistic_forget]
    exact regularStatistic_second b lam hlam hKS ℓ i
  rw [advantage_eq_integral]
  apply estimator_tv_lower (p := p) hB (ksConstant_pos hKS)
  · rw [integral_discreteMarginal p hB, hmean 0, hmean 1, hmean 2]
    norm_num [spinScore, show (1:Spin) ≠ 0 by decide, show (2:Spin) ≠ 0 by decide]
  · exact hmean 0
  · have hB₂ (o : Observation ℓ) : |f o^2| ≤ B^2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      have hh : |f o| ≤ B := hB o
      nlinarith [hh, sq_abs (f o), abs_nonneg (f o)]
    rw [integral_discreteMarginal p hB₂]
    linarith [hsecond 0, hsecond 1, hsecond 2]

theorem regular_reconstructs_above_KS (b : ℕ) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (b:ℝ)*lam^2) : Reconstructs lam hlam (PMF.pure b) := by
  refine ⟨⨅ ℓ, advantage lam hlam (PMF.pure b) ℓ, ?_, advantage_tendsto _ _ _⟩
  have he : 1/(3*ksConstant b lam) ≤ ⨅ ℓ, advantage lam hlam (PMF.pure b) ℓ := by
    exact le_ciInf (fun ℓ ↦ regular_estimator_advantage b lam hlam hKS ℓ)
  exact (div_pos (by norm_num) (mul_pos (by norm_num) (ksConstant_pos hKS))).trans_le he

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
open scoped BigOperators Topology
open ThreeState.TreeClauses.Experiment

namespace OAI
namespace ThreeState.TreeClauses.Tree
theorem _root_.solution (b : ℕ) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (b:ℝ)*lam^2) : Reconstructs lam hlam (PMF.pure b) := by
  first
    | exact OAI.ThreeState.TreeClauses.Tree.regular_reconstructs_above_KS b lam hlam hKS
    | exact OAI.ThreeState.TreeClauses.Tree.regular_reconstructs_above_KS
    | (apply OAI.ThreeState.TreeClauses.Tree.regular_reconstructs_above_KS <;> assumption)
    | (intros; apply OAI.ThreeState.TreeClauses.Tree.regular_reconstructs_above_KS <;> assumption)
end ThreeState.TreeClauses.Tree
end OAI
