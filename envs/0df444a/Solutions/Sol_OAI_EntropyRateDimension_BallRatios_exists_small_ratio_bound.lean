-- Prove2me | solution 1 for OAI.EntropyRateDimension.BallRatios.exists_small_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:13:29.33756+00:00
-- url     : https://prove2.me/submissions/c2e7c2ae-dd22-41d9-b793-ef0744ddcc96

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.BallRatios
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology


theorem solution : ∃ N : ℕ, ∀ (μ ν : Measure ℝ) (t : ℝ≥0∞)
    (E : Set ℝ),
    (∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ν (closedBall x r) ≤ t*μ (closedBall x r)) →
    ν E ≤ N*t*μ univ := by
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := ℝ)
  refine ⟨N, fun μ ν t E hE => ?_⟩
  choose! r hr0 hr1 hrt using hE
  let q : Besicovitch.BallPackage E ℝ :=
    { c := fun x => x.1, r := fun x => r x.1, rpos := fun x => hr0 x.1 x.2, r_bound := 1,
      r_le := fun x => hr1 x.1 x.2 }
  obtain ⟨s, hsd, hcov⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
  have hsd' : ∀ i, (s i).PairwiseDisjoint (fun j : E => Metric.closedBall (j:ℝ) (r j)) := hsd
  have hcount : ∀ i, (s i).Countable := by
    intro i
    have hd : (s i).PairwiseDisjoint (fun j : E => Metric.ball (j:ℝ) (r j)) :=
      (hsd' i).mono (fun j => Metric.ball_subset_closedBall)
    exact hd.countable_of_isOpen (fun j _ => Metric.isOpen_ball)
      (fun j _ => Metric.nonempty_ball.2 (hr0 j.1 j.2))
  have hEsub : E ⊆ ⋃ i, ⋃ j ∈ s i, Metric.closedBall (j:ℝ) (r j) := by
    intro x hx
    have h := hcov ⟨⟨x, hx⟩, rfl⟩
    simp only [Set.mem_iUnion] at h ⊢
    obtain ⟨i, j, hj, hxj⟩ := h
    exact ⟨i, j, hj, Metric.ball_subset_closedBall hxj⟩
  calc ν E ≤ ν (⋃ i, ⋃ j ∈ s i, Metric.closedBall (j:ℝ) (r j)) := measure_mono hEsub
    _ ≤ ∑ i, ν (⋃ j ∈ s i, Metric.closedBall (j:ℝ) (r j)) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ∑' j : s i, ν (Metric.closedBall (j:ℝ) (r j)) :=
        Finset.sum_le_sum fun i _ => measure_biUnion_le _ (hcount i) _
    _ ≤ ∑ i, ∑' j : s i, t * μ (Metric.closedBall (j:ℝ) (r j)) :=
        Finset.sum_le_sum fun i _ => ENNReal.tsum_le_tsum fun j => hrt j.1.1 j.1.2
    _ = ∑ i, t * μ (⋃ j ∈ s i, Metric.closedBall (j:ℝ) (r j)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ENNReal.tsum_mul_left, measure_biUnion (hcount i) (hsd' i)
          (fun _ _ => measurableSet_closedBall)]
    _ ≤ ∑ i : Fin N, t * μ Set.univ :=
        Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (measure_mono (Set.subset_univ _))
    _ = N * t * μ Set.univ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

