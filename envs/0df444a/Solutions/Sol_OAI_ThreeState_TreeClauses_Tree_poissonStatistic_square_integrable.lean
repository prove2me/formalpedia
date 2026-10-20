-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Tree.poissonStatistic_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:44:00.267857+00:00
-- url     : https://prove2.me/submissions/075d19ce-f97e-49f1-98fc-903bd3b4f97a

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/PoissonReconstruction.lean:L37-L60
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Tree.poissonStatistic_square_integrable. The node keeps its source
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

-- ---- from OAI.Probability.ThreeStateClauses.BranchMoments ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Branch Moments. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

variable {ι : Type*} [Fintype ι]

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
  {μ : Measure X} [SigmaFinite μ] {a u : X → ℝ}

omit [MeasurableSpace X] in
lemma select_pair_product (a u : X → ℝ) (x : ι → X) (j k : ι) :
    weightProduct a x*(u (x j)*u (x k)) =
      ∏ i, a (x i)*(if i=j then u (x i) else 1)*(if i=k then u (x i) else 1) := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [weightProduct, Fintype.prod_ite_eq']
  ring

lemma integrable_weighted_pair (ha : Integrable a μ) (hau : Integrable (fun x ↦ a x*u x) μ)
    (hau₂ : Integrable (fun x ↦ a x*u x^2) μ) (j k : ι) :
    Integrable (fun x : ι → X ↦ weightProduct a x*(u (x j)*u (x k))) (Measure.pi fun _ ↦ μ) := by
  have hi : ∀ i : ι, Integrable (fun x ↦ a x*(if i=j then u x else 1)*(if i=k then u x else 1)) μ := by
    intro i
    by_cases h : i=j <;> by_cases h' : i=k
    · simpa only [ite_eq_left h, ite_eq_left h', pow_two, mul_assoc] using hau₂
    · simpa only [ite_eq_left h, ite_eq_right h', mul_one] using hau
    · simpa only [ite_eq_right h, ite_eq_left h', mul_one] using hau
    · simpa [h, h'] using ha
  simpa only [← select_pair_product] using Integrable.fintype_prod hi

lemma integrable_weighted_sq_sum (ha : Integrable a μ) (hau : Integrable (fun x ↦ a x*u x) μ)
    (hau₂ : Integrable (fun x ↦ a x*u x^2) μ) :
    Integrable (fun x : ι → X ↦ weightProduct a x*(∑ j, u (x j))^2) (Measure.pi fun _ ↦ μ) := by
  have he (x : ι → X) : weightProduct a x*(∑ j, u (x j))^2 =
      ∑ j, ∑ k, weightProduct a x*(u (x j)*u (x k)) := by
    rw [sq, Finset.sum_mul_sum]
    simp_rw [Finset.mul_sum]
  simp_rw [he]
  exact integrable_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ integrable_weighted_pair ha hau hau₂ j k))

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
-- [generator] trimmed: open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive
open ThreeState.TreeClauses.Radial

end ThreeState.TreeClauses.Experiment

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

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma product_square_sum_integrable (p : PMF α) {f : α → ℝ}
    (hf : Integrable (fun a ↦ f a^2) p.toMeasure) (n : ℕ) :
    Integrable (fun v : Fin n → α ↦ (∑ j, f (v j))^2) (productPMF (fun _ ↦ p)).toMeasure := by
  rw [productPMF_measure]
  simpa [weightProduct] using integrable_weighted_sq_sum (ι := Fin n) (a := fun _ : α ↦ (1:ℝ))
    (u := f) (integrable_const 1) (by simpa using pmf_integrable_of_square p hf) (by simpa using hf)

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

lemma sigmaPMF_integrable (ρ : PMF ℕ) (p : ∀ n, PMF (β n)) {f : Sigma β → ℝ}
    (hf : ∀ n, Integrable (fun a ↦ f ⟨n,a⟩) (p n).toMeasure)
    (hn : Integrable (fun n ↦ ∫ a, |f ⟨n,a⟩| ∂(p n).toMeasure) ρ.toMeasure) :
    Integrable f (sigmaPMF ρ p).toMeasure := by
  rw [sigmaPMF_eq_bind]
  apply pmf_integrable_bind
  · intro n
    exact (pmf_integrable_map_iff (p n) (Sigma.mk n) f).2 (hf n)
  · simpa only [integral_pmf_map] using hn

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

lemma poissonStatistic_square_integrable (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (ℓ : ℕ) (i : Spin) :
    Integrable (fun v ↦ orderedStatistic d lam ℓ v^2)
      (orderedLaw (poissonPMF d) lam hlam ℓ i).toMeasure := by
  induction ℓ generalizing i with
  | zero => exact Integrable.of_finite
  | succ ℓ ih =>
    let p := (channel lam hlam i).bind (orderedLaw (poissonPMF d) lam hlam ℓ)
    have hp : Integrable (fun v ↦ orderedStatistic d lam ℓ v^2) p.toMeasure :=
      pmf_integrable_bind_finite _ _ ih
    change Integrable (fun z : Σ n, Fin n → OrderedObservation ℓ ↦
      ((∑ j, orderedStatistic d lam ℓ (z.2 j))/((d:ℝ)*lam))^2)
      (sigmaPMF (poissonPMF d) (fun n ↦ productPMF (fun _ : Fin n ↦ p))).toMeasure
    apply sigmaPMF_integrable
    · intro n
      simpa only [div_pow] using (product_square_sum_integrable p hp n).div_const (((d:ℝ)*lam)^2)
    · change Integrable (fun n ↦ ∫ v : Fin n → OrderedObservation ℓ,
        |((∑ j, orderedStatistic d lam ℓ (v j))/((d:ℝ)*lam))^2|
        ∂(productPMF (fun _ : Fin n ↦ p)).toMeasure) (poissonPMF d).toMeasure
      have hab (x : ℝ) : |x^2| = x^2 := abs_of_nonneg (sq_nonneg x)
      simp_rw [hab, div_pow, integral_div,
        integral_product_sq_sum_integrable p hp]
      exact (((poisson_integrable_first d).mul_const _).add
        (((poisson_integrable_second d).sub (poisson_integrable_first d)).mul_const _)).div_const _

end ThreeState.TreeClauses.Tree

end 

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability

end ThreeState.TreeClauses.Tree

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators NNReal
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Tree.poissonStatistic_square_integrable := @_root_.OAI.ThreeState.TreeClauses.Tree.poissonStatistic_square_integrable
