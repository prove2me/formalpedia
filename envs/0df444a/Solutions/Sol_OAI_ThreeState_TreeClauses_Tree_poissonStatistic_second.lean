-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Tree.poissonStatistic_second
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:48:34.854909+00:00
-- url     : https://prove2.me/submissions/0fa16bee-5e1c-4620-9289-5f737cb790fa

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/PoissonReconstruction.lean:L114-L160
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Tree.poissonStatistic_second. The node keeps its source
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
import Definitions.Def_OAI_Probability_ThreeStateClauses_PoissonReconstruction
import Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_integral_weighted_sq_sum
import Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_poissonStatistic_mean
import Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_poissonStatistic_square_integrable

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

end ThreeState.TreeClauses.Tree

end

end OAI

-- ---- from OAI.Probability.ThreeStateClauses.ObservedMixtures ----
namespace OAI

/-! Observed Mixtures. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {X : Type*} [MeasurableSpace X]

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {α : ℕ → Type*}

lemma sigmaPMF_eq_bind (ρ : PMF ℕ) (p : ∀ n, PMF (α n)) :
    sigmaPMF ρ p = ρ.bind (fun n ↦ (p n).map (Sigma.mk n)) := by
  classical
  apply PMF.ext
  rintro ⟨n,a⟩
  rw [PMF.bind_apply, tsum_eq_single n]
  · simp [PMF.map_apply]
  · intro m hm
    have hn : n ≠ m := Ne.symm hm
    simp [PMF.map_apply, hn]

section Measures
variable [∀ n, Countable (α n)] [∀ n, MeasurableSpace (α n)]
  [∀ n, MeasurableSingletonClass (α n)]

end Measures
end ThreeState.TreeClauses.Experiment

end

end OAI

-- ---- from OAI.Probability.ThreeStateClauses.PoissonMoments ----
namespace OAI

/-! Poisson Moments. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace ThreeState.TreeClauses.Probability

lemma poissonWeight_succ (t : ℝ) (n : ℕ) :
    poissonWeight t (n+1)*((n:ℝ)+1) = t*poissonWeight t n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma poissonWeight_mean (t : ℝ≥0) : HasSum (fun n ↦ poissonWeight t n*(n:ℝ)) t := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero,
    Nat.cast_add, Nat.cast_one, poissonWeight_succ]
  simpa using (poissonWeight_mass t).mul_left (t:ℝ)

lemma poissonWeight_factorial_second (t : ℝ≥0) :
    HasSum (fun n ↦ poissonWeight t n*((n:ℝ)^2-n)) ((t:ℝ)^2) := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
    sub_self, mul_zero, sub_zero]
  have he (n : ℕ) : poissonWeight t (n+1)*(((n+1:ℕ):ℝ)^2-((n+1:ℕ):ℝ)) =
      (t:ℝ)*(poissonWeight t n*(n:ℝ)) := by
    push_cast
    calc
      _ = (poissonWeight t (n+1)*((n:ℝ)+1))*(n:ℝ) := by ring
      _ = _ := by rw [poissonWeight_succ]; ring
  simp_rw [he]
  simpa [pow_two] using (poissonWeight_mean t).mul_left (t:ℝ)

lemma poissonWeight_second (t : ℝ≥0) :
    HasSum (fun n ↦ poissonWeight t n*(n:ℝ)^2) ((t:ℝ)^2+t) := by
  have h := (poissonWeight_factorial_second t).add (poissonWeight_mean t)
  convert h using 1
  ext n; ring

lemma poissonPMF_real (t : ℝ≥0) (n : ℕ) : (poissonPMF t n).toReal = poissonWeight t n := by
  change (ENNReal.ofReal (poissonWeight t n)).toReal = _
  exact ENNReal.toReal_ofReal (poissonWeight_nonneg t.coe_nonneg n)

lemma poissonPMF_toMeasure (t : ℝ≥0) : (poissonPMF t).toMeasure = poissonMeasure t := by
  apply Measure.ext_of_singleton
  intro n
  rw [PMF.toMeasure_apply_singleton, poissonMeasure_singleton]
  · rfl
  · exact measurableSet_singleton n

lemma poisson_integrable_first (t : ℝ≥0) : Integrable (fun n : ℕ ↦ (n:ℝ)) (poissonPMF t).toMeasure := by
  rw [poissonPMF_toMeasure, integrable_poissonMeasure_iff]
  simpa only [Real.norm_eq_abs, Nat.abs_cast, smul_eq_mul, poissonWeight] using (poissonWeight_mean t).summable

lemma poisson_integrable_second (t : ℝ≥0) : Integrable (fun n : ℕ ↦ (n:ℝ)^2) (poissonPMF t).toMeasure := by
  rw [poissonPMF_toMeasure, integrable_poissonMeasure_iff]
  simpa only [Real.norm_eq_abs, abs_pow, Nat.abs_cast, smul_eq_mul, poissonWeight] using (poissonWeight_second t).summable

lemma poisson_integral_first (t : ℝ≥0) : (∫ n : ℕ, (n:ℝ) ∂(poissonPMF t).toMeasure) = t := by
  rw [PMF.integral_eq_tsum _ _ (poisson_integrable_first t)]
  simpa only [poissonPMF_real, smul_eq_mul] using (poissonWeight_mean t).tsum_eq

lemma poisson_integral_second (t : ℝ≥0) : (∫ n : ℕ, (n:ℝ)^2 ∂(poissonPMF t).toMeasure) = (t:ℝ)^2+t := by
  rw [PMF.integral_eq_tsum _ _ (poisson_integrable_second t)]
  simpa only [poissonPMF_real, smul_eq_mul] using (poissonWeight_second t).tsum_eq

lemma poisson_integral_factorial_second (t : ℝ≥0) :
    (∫ n : ℕ, ((n:ℝ)^2-n) ∂(poissonPMF t).toMeasure) = (t:ℝ)^2 := by
  rw [integral_sub (poisson_integrable_second t) (poisson_integrable_first t),
    poisson_integral_second, poisson_integral_first]
  ring

end ThreeState.TreeClauses.Probability

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

lemma pmf_integrable_of_square (p : PMF α) {f : α → ℝ}
    (hf : Integrable (fun a ↦ f a^2) p.toMeasure) : Integrable f p.toMeasure := by
  apply ((integrable_const (1:ℝ)).add hf).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun a ↦ by
    simp only [Real.norm_eq_abs, Pi.add_apply]
    nlinarith [sq_nonneg (|f a|-1), sq_abs (f a)])

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma integral_product_sq_sum_integrable (p : PMF α) {f : α → ℝ}
    (hf : Integrable (fun a ↦ f a^2) p.toMeasure) (n : ℕ) :
    (∫ v : Fin n → α, (∑ j, f (v j))^2 ∂(productPMF (fun _ ↦ p)).toMeasure) =
      (n:ℝ)*(∫ a, f a^2 ∂p.toMeasure)+((n:ℝ)^2-n)*(∫ a, f a ∂p.toMeasure)^2 := by
  rw [productPMF_measure]
  simpa [weightProduct] using integral_weighted_sq_sum (ι := Fin n) (a := fun _ : α ↦ (1:ℝ))
    (u := f) (integrable_const 1) (by simpa using pmf_integrable_of_square p hf)
    (by simpa using hf) (by simp)

section Sigma
variable {β : ℕ → Type*} [∀ n, Countable (β n)] [∀ n, MeasurableSpace (β n)]
  [∀ n, MeasurableSingletonClass (β n)]

lemma integral_sigmaPMF_integrable (ρ : PMF ℕ) (p : ∀ n, PMF (β n)) {f : Sigma β → ℝ}
    (hf : Integrable f (sigmaPMF ρ p).toMeasure) :
    (∫ z, f z ∂(sigmaPMF ρ p).toMeasure) = ∫ n, (∫ a, f ⟨n,a⟩ ∂(p n).toMeasure) ∂ρ.toMeasure := by
  rw [sigmaPMF_eq_bind] at hf ⊢
  rw [integral_pmf_bind_integrable _ _ hf]
  simp only [integral_pmf_map]

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

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability

lemma poissonKSConstant_ge_four {d lam : ℝ} (hKS : 1 < d*lam^2) : 4 ≤ poissonKSConstant d lam := by
  rw [poissonKSConstant, le_div_iff₀ (by linarith)]
  linarith

lemma poissonKSConstant_identity {d lam : ℝ} (hKS : 1 < d*lam^2) :
    poissonKSConstant d lam*(d*lam^2-1) = 4*(d*lam^2) := by
  rw [poissonKSConstant, div_mul_cancel₀ _ (by linarith)]

lemma poissonStatistic_second (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (d:ℝ)*lam^2) (ℓ : ℕ) (i : Spin) :
    (∫ v, orderedStatistic d lam ℓ v^2
      ∂(orderedLaw (poissonPMF d) lam hlam ℓ i).toMeasure) ≤ poissonKSConstant d lam := by
  have hd : 0 < (d:ℝ) := by
    by_contra h
    have he : (d:ℝ) = 0 := le_antisymm (not_lt.mp h) d.coe_nonneg
    norm_num [he] at hKS
  have hl : lam ≠ 0 := by intro h; norm_num [h] at hKS
  have hden : 0 < ((d:ℝ)*lam)^2 := sq_pos_of_ne_zero (mul_ne_zero hd.ne' hl)
  induction ℓ generalizing i with
  | zero =>
    change (∫ v : Spin, spinScore v^2 ∂(PMF.pure i).toMeasure) ≤ _
    rw [PMF.toMeasure_pure, integral_dirac]
    exact (spinScore_square i).trans (poissonKSConstant_ge_four hKS)
  | succ ℓ ih =>
    let p := (channel lam hlam i).bind (orderedLaw (poissonPMF d) lam hlam ℓ)
    have hp₂ : Integrable (fun v ↦ orderedStatistic d lam ℓ v^2) p.toMeasure :=
      pmf_integrable_bind_finite _ _ (poissonStatistic_square_integrable d lam hlam ℓ)
    have hp := pmf_integrable_of_square p hp₂
    have hmean : (∫ v, orderedStatistic d lam ℓ v ∂p.toMeasure) = lam*spinScore i := by
      rw [integral_pmf_bind_integrable _ _ hp]
      simp_rw [poissonStatistic_mean d hd.ne' lam hlam hl ℓ]
      exact channel_spinScore lam hlam i
    have hsecond : (∫ v, orderedStatistic d lam ℓ v^2 ∂p.toMeasure) ≤ poissonKSConstant d lam := by
      rw [integral_pmf_bind_integrable _ _ hp₂]
      exact (integral_mono Integrable.of_finite (integrable_const _) ih).trans_eq (by simp)
    have hi := poissonStatistic_square_integrable d lam hlam (ℓ+1) i
    change (∫ z : Σ n, Fin n → OrderedObservation ℓ,
      ((∑ j, orderedStatistic d lam ℓ (z.2 j))/((d:ℝ)*lam))^2
      ∂(sigmaPMF (poissonPMF d) (fun n ↦ productPMF (fun _ : Fin n ↦ p))).toMeasure) ≤ _
    change Integrable (fun z : Σ n, Fin n → OrderedObservation ℓ ↦
      ((∑ j, orderedStatistic d lam ℓ (z.2 j))/((d:ℝ)*lam))^2)
      (sigmaPMF (poissonPMF d) (fun n ↦ productPMF (fun _ : Fin n ↦ p))).toMeasure at hi
    rw [integral_sigmaPMF_integrable _ _ hi]
    simp_rw [div_pow, integral_div, integral_product_sq_sum_integrable p hp₂]
    rw [hmean, integral_add
      (f := fun n : ℕ ↦ (n:ℝ)*(∫ v, orderedStatistic d lam ℓ v^2 ∂p.toMeasure))
      (g := fun n : ℕ ↦ ((n:ℝ)^2-n)*(lam*spinScore i)^2)
      ((poisson_integrable_first d).mul_const _)
      (((poisson_integrable_second d).sub (poisson_integrable_first d)).mul_const _),
      integral_mul_const, integral_mul_const, poisson_integral_first, poisson_integral_factorial_second]
    apply (div_le_iff₀ hden).2
    have hs := mul_le_mul_of_nonneg_left (spinScore_square i) (sq_nonneg ((d:ℝ)*lam))
    have hm := mul_le_mul_of_nonneg_left hsecond hd.le
    have hid := congrArg (fun x : ℝ ↦ x*(d:ℝ)) (poissonKSConstant_identity hKS)
    nlinarith only [hs,hm,hid]

end ThreeState.TreeClauses.Tree

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Tree.poissonStatistic_second := @_root_.OAI.ThreeState.TreeClauses.Tree.poissonStatistic_second
