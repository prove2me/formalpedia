-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Tree.regularStatistic_mean
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:36:07.082884+00:00
-- url     : https://prove2.me/submissions/bd22577d-dd56-442a-87ee-2f39e47712f4

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/RegularStatistics.lean:L112-L126
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Tree.regularStatistic_mean. The node keeps its source
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
import Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_integral_pmf_bind

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
lemma select_product (a u : X → ℝ) (x : ι → X) (j : ι) :
    weightProduct a x*u (x j) = ∏ i, a (x i)*(if i=j then u (x i) else 1) := by
  rw [Finset.prod_mul_distrib]
  simp only [weightProduct, Fintype.prod_ite_eq']

lemma integrable_weighted_single (ha : Integrable a μ) (hau : Integrable (fun x ↦ a x*u x) μ)
    (j : ι) : Integrable (fun x : ι → X ↦ weightProduct a x*u (x j)) (Measure.pi fun _ ↦ μ) := by
  have hi : ∀ i : ι, Integrable (fun x ↦ a x*(if i=j then u x else 1)) μ := by
    intro i
    by_cases h : i=j
    · simpa [h] using hau
    · simpa [h] using ha
  simpa only [← select_product] using Integrable.fintype_prod hi

lemma integral_weighted_single (ha : ∫ x, a x ∂μ = 1) (j : ι) :
    (∫ x : ι → X, weightProduct a x*u (x j) ∂(Measure.pi fun _ ↦ μ)) = ∫ x, a x*u x ∂μ := by
  simp_rw [select_product]
  rw [integral_fintype_prod_eq_prod (fun i x ↦ a x*(if i=j then u x else 1))]
  have he (i : ι) : (∫ x, a x*(if i=j then u x else 1) ∂μ) =
      if i=j then (∫ x, a x*u x ∂μ) else 1 := by
    by_cases h : i=j <;> simp [h, ha]
  simp_rw [he]
  simp

lemma integral_weighted_sum (ha : Integrable a μ) (hau : Integrable (fun x ↦ a x*u x) μ)
    (hbal : ∫ x, a x ∂μ = 1) :
    (∫ x : ι → X, weightProduct a x*(∑ j, u (x j)) ∂(Measure.pi fun _ ↦ μ)) =
      (Fintype.card ι : ℝ)*(∫ x, a x*u x ∂μ) := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ ↦ integrable_weighted_single ha hau j)]
  simp only [integral_weighted_single hbal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

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

lemma integral_product_sum (p : PMF α) (f : α → ℝ) (n : ℕ) :
    (∫ v : Fin n → α, (∑ j, f (v j)) ∂(productPMF (fun _ ↦ p)).toMeasure) =
      (n:ℝ)*(∫ a, f a ∂p.toMeasure) := by
  rw [productPMF_measure]
  simpa [weightProduct] using integral_weighted_sum (ι := Fin n) (a := fun _ : α ↦ (1:ℝ))
    (u := f) (integrable_const 1) Integrable.of_finite (by simp)

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

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

lemma regularStatistic_mean (b : ℕ) (hb : 0 < b) (lam : ℝ) (hlam : Admissible lam)
    (hl : lam ≠ 0) (ℓ : ℕ) (i : Spin) :
    (∫ v, regularStatistic b lam ℓ v ∂(regularLaw b lam hlam ℓ i).toMeasure) = spinScore i := by
  have hb' : (b:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  induction ℓ generalizing i with
  | zero =>
    change (∫ v : Spin, spinScore v ∂(PMF.pure i).toMeasure) = spinScore i
    rw [PMF.toMeasure_pure, integral_dirac]
  | succ ℓ ih =>
    change (∫ v, (∑ j : Fin b, regularStatistic b lam ℓ (v j))/((b:ℝ)*lam)
      ∂(productPMF (fun _ ↦ (channel lam hlam i).bind (regularLaw b lam hlam ℓ))).toMeasure) = _
    rw [integral_div, integral_product_sum, integral_pmf_bind_finite]
    simp_rw [ih]
    rw [channel_spinScore]
    field_simp

end ThreeState.TreeClauses.Tree

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators
open ThreeState.TreeClauses.Experiment


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Tree.regularStatistic_mean := @_root_.OAI.ThreeState.TreeClauses.Tree.regularStatistic_mean
