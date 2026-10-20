-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Experiment.integral_weighted_sq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:30:19.835493+00:00
-- url     : https://prove2.me/submissions/a0be7f48-6d3e-437a-98da-770720db49bc

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/BranchMoments.lean:L201-L218
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Experiment.integral_weighted_sq_sum. The node keeps its source
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
lemma select_product (a u : X → ℝ) (x : ι → X) (j : ι) :
    weightProduct a x*u (x j) = ∏ i, a (x i)*(if i=j then u (x i) else 1) := by
  rw [Finset.prod_mul_distrib]
  simp only [weightProduct, Fintype.prod_ite_eq']

lemma integral_weighted_single (ha : ∫ x, a x ∂μ = 1) (j : ι) :
    (∫ x : ι → X, weightProduct a x*u (x j) ∂(Measure.pi fun _ ↦ μ)) = ∫ x, a x*u x ∂μ := by
  simp_rw [select_product]
  rw [integral_fintype_prod_eq_prod (fun i x ↦ a x*(if i=j then u x else 1))]
  have he (i : ι) : (∫ x, a x*(if i=j then u x else 1) ∂μ) =
      if i=j then (∫ x, a x*u x ∂μ) else 1 := by
    by_cases h : i=j <;> simp [h, ha]
  simp_rw [he]
  simp

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

lemma integral_weighted_pair (ha : ∫ x, a x ∂μ = 1) (j k : ι) :
    (∫ x : ι → X, weightProduct a x*(u (x j)*u (x k)) ∂(Measure.pi fun _ ↦ μ)) =
      if j=k then (∫ x, a x*u x^2 ∂μ) else (∫ x, a x*u x ∂μ)^2 := by
  by_cases hjk : j=k
  · subst k
    simp only [ite_true, pow_two]
    exact integral_weighted_single (u := fun x ↦ u x*u x) ha j
  · simp_rw [select_pair_product]
    rw [integral_fintype_prod_eq_prod (fun i x ↦ a x*(if i=j then u x else 1)*(if i=k then u x else 1)), ite_eq_right hjk]
    have he (i : ι) : (∫ x, a x*(if i=j then u x else 1)*(if i=k then u x else 1) ∂μ) =
        (if i=j then (∫ x, a x*u x ∂μ) else 1)*(if i=k then (∫ x, a x*u x ∂μ) else 1) := by
      by_cases h : i=j <;> by_cases h' : i=k
      · exact (hjk (h.symm.trans h')).elim
      · simp only [ite_eq_left h, ite_eq_right h', mul_one]
      · simp only [ite_eq_right h, ite_eq_left h', mul_one, one_mul]
      · simp only [ite_eq_right h, ite_eq_right h', mul_one, ha]
    simp_rw [he]
    rw [Finset.prod_mul_distrib]
    simp [sq]

theorem integral_weighted_sq_sum (ha : Integrable a μ) (hau : Integrable (fun x ↦ a x*u x) μ)
    (hau₂ : Integrable (fun x ↦ a x*u x^2) μ) (hbal : ∫ x, a x ∂μ = 1) :
    (∫ x : ι → X, weightProduct a x*(∑ j, u (x j))^2 ∂(Measure.pi fun _ ↦ μ)) =
      (Fintype.card ι : ℝ)*(∫ x, a x*u x^2 ∂μ)+
      ((Fintype.card ι : ℝ)^2-(Fintype.card ι : ℝ))*(∫ x, a x*u x ∂μ)^2 := by
  have he (x : ι → X) : weightProduct a x*(∑ j, u (x j))^2 =
      ∑ j, ∑ k, weightProduct a x*(u (x j)*u (x k)) := by
    rw [sq, Finset.sum_mul_sum]
    simp_rw [Finset.mul_sum]
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ integrable_weighted_pair ha hau hau₂ j k))]
  simp_rw [integral_finsetSum _ (fun k _ ↦ integrable_weighted_pair ha hau hau₂ _ k), integral_weighted_pair hbal]
  have he' (j k : ι) : (if j=k then (∫ x, a x*u x^2 ∂μ) else (∫ x, a x*u x ∂μ)^2) =
      (if j=k then (∫ x, a x*u x^2 ∂μ)-(∫ x, a x*u x ∂μ)^2 else 0)+(∫ x, a x*u x ∂μ)^2 := by
    split_ifs <;> ring
  simp_rw [he', Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

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

-- ---- platform node ----
open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Experiment
open scoped BigOperators ENNReal NNReal Topology
open Filter
open MeasureTheory
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Experiment.integral_weighted_sq_sum := @_root_.OAI.ThreeState.TreeClauses.Experiment.integral_weighted_sq_sum
