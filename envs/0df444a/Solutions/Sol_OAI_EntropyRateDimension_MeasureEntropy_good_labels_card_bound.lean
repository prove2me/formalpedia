-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.good_labels_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:58:47.493317+00:00
-- url     : https://prove2.me/submissions/ba5bd729-9e7b-4899-8f12-fe876f5678ce

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ
open scoped BigOperators ENNReal
open MeasureTheory
theorem h41n_card_q (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : Finset ℤ) (x : ℤ → ℝ)
    (r q : ℝ) (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → 2*r ≤ dist (x i) (x j))
    (hq : ∀ i ∈ t, q ≤ μ.real (Metric.ball (x i) r)) : (t.card : ℝ) * q ≤ 1 := by
  have hpd : (↑t : Set ℤ).PairwiseDisjoint (fun i => Metric.ball (x i) r) := by
    intro i hi j hj hij
    exact Metric.ball_disjoint_ball (by linarith [hdisj i hi j hj hij])
  calc (t.card : ℝ) * q = ∑ i ∈ t, q := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ t, μ.real (Metric.ball (x i) r) := Finset.sum_le_sum hq
    _ = μ.real (⋃ i ∈ t, Metric.ball (x i) r) :=
        (measureReal_biUnion_finset hpd (fun _ _ => Metric.isOpen_ball.measurableSet)).symm
    _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
    _ = 1 := by simp

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s u q : ℝ} (hs : 0 < s) (a : Finset ℤ) (x : ℤ → ℝ)
    (hx : ∀ i ∈ a, label s u (x i)=i)
    (hq : ∀ i ∈ a, q ≤ μ.real (Metric.ball (x i) (s/2))) :
    (a.card : ℝ)*q ≤ 3 := by
  classical
  have key : ∀ t ⊆ a, (∀ i ∈ t, ∀ j ∈ t, i ≠ j → i + 2 ≤ j ∨ j + 2 ≤ i) →
      (t.card : ℝ) * q ≤ 1 := by
    intro t ht hsep
    apply h41n_card_q μ t x (s/2) q _ (fun i hi => hq i (ht hi))
    have sep1 : ∀ i ∈ t, ∀ j ∈ t, i + 2 ≤ j → s ≤ x j - x i := by
      intro i hi j hj h
      have hfi := hx i (ht hi)
      have hfj := hx j (ht hj)
      simp only [label, Int.floor_eq_iff] at hfi hfj
      have h' : (i:ℝ) + 2 ≤ j := by exact_mod_cast h
      have h1 : 1 ≤ x j / s - x i / s := by linarith
      have e : x j - x i = s * (x j / s - x i / s) := by field_simp
      rw [e]; nlinarith
    intro i hi j hj hij
    rw [Real.dist_eq]
    rcases hsep i hi j hj hij with h | h
    · have := sep1 i hi j hj h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have := sep1 j hj i hi h
      rw [abs_of_nonneg (by linarith)]; linarith
  have h1 := key (a.filter (fun i => Even i)) (Finset.filter_subset _ _) (by
    intro i hi j hj hij
    simp only [Finset.mem_filter, Int.even_iff] at hi hj
    omega)
  have h2 := key (a.filter (fun i => ¬ Even i)) (Finset.filter_subset _ _) (by
    intro i hi j hj hij
    simp only [Finset.mem_filter, Int.not_even_iff] at hi hj
    omega)
  have hc := Finset.card_filter_add_card_filter_not (s := a) (fun i => Even i)
  have hc' : (a.card : ℝ) = ((a.filter (fun i => Even i)).card : ℝ) +
      ((a.filter (fun i => ¬ Even i)).card : ℝ) := by exact_mod_cast hc.symm
  rw [hc', add_mul]
  linarith

