-- Prove2me | solution 1 for OAI.ProjectionMoments.Weighted.eval_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:54:22.613656+00:00
-- url     : https://prove2.me/submissions/6ad17af2-7ac7-4d9a-bf62-c6037625b4d4

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover

open OAI OAI.ProjectionMoments OAI.ProjectionMoments.Weighted
open scoped Topology BigOperators Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
variable {ι : Type*}
theorem solution {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i)
    (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite) {K : ℝ} (hK : 0 ≤ K)
    {v : ι → ℝ} (hv : ∀ i, v i ∈ Icc (0:ℝ) 1) :
    ContinuousOn (fun a : ι → ℝ => ∑' i, a i*v i) (budget b K) := by
  classical
  let S : ℕ → Finset ι := fun n => (hproper n).toFinset
  have hmemS : ∀ n i, i ∈ S n ↔ b i ≤ n := fun n i => by simp [S]
  have hsb : ∀ a ∈ budget b K, Summable (fun i => a i * b i) := by
    rintro a ⟨ha0, haK⟩
    exact summable_of_sum_le (fun i => mul_nonneg (ha0 i) (by linarith [hb i])) haK
  have hsv : ∀ a ∈ budget b K, Summable (fun i => a i * v i) := by
    intro a ha
    refine (hsb a ha).of_nonneg_of_le (fun i => mul_nonneg (ha.1 i) (hv i).1) (fun i => ?_)
    exact mul_le_mul_of_nonneg_left (by linarith [(hv i).2, hb i]) (ha.1 i)
  have htail : ∀ n : ℕ, 0 < n → ∀ a ∈ budget b K,
      |(∑' i, a i * v i) - ∑ i ∈ S n, a i * v i| ≤ K / n := by
    intro n hn a ha
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hti : ∀ i, 0 ≤ (if i ∈ S n then 0 else a i * v i) := fun i => by
      split_ifs
      · exact le_refl 0
      · exact mul_nonneg (ha.1 i) (hv i).1
    have hg : Summable (fun i => if i ∈ S n then a i * v i else 0) :=
      summable_of_ne_finset_zero (s := S n) (fun i hi => if_neg hi)
    have hgsum : (∑' i, (if i ∈ S n then a i * v i else 0)) = ∑ i ∈ S n, a i * v i := by
      rw [tsum_eq_sum (s := S n) (fun i hi => if_neg hi)]
      exact Finset.sum_congr rfl (fun i hi => if_pos hi)
    have hsplit : (∑' i, a i * v i) - ∑ i ∈ S n, a i * v i =
        ∑' i, (if i ∈ S n then 0 else a i * v i) := by
      rw [← hgsum, ← (hsv a ha).tsum_sub hg]
      refine tsum_congr (fun i => ?_)
      split_ifs <;> ring
    have hnonneg : 0 ≤ ∑' i, (if i ∈ S n then 0 else a i * v i) := tsum_nonneg hti
    have hle : (∑' i, (if i ∈ S n then 0 else a i * v i)) ≤ ∑' i, a i * b i / n := by
      refine Summable.tsum_le_tsum (fun i => ?_) ?_ ((hsb a ha).div_const _)
      · split_ifs with hi
        · exact div_nonneg (mul_nonneg (ha.1 i) (by linarith [hb i])) hnr.le
        · have hbi : (n : ℝ) < b i := by rw [hmemS] at hi; push_neg at hi; exact hi
          rw [le_div_iff₀ hnr]
          have h1 : a i * v i ≤ a i := by nlinarith [ha.1 i, (hv i).1, (hv i).2]
          have h2 : a i * n ≤ a i * b i := mul_le_mul_of_nonneg_left hbi.le (ha.1 i)
          nlinarith
      · exact (hsv a ha).of_nonneg_of_le hti (fun i => by
          split_ifs
          · exact mul_nonneg (ha.1 i) (hv i).1
          · exact le_refl _)
    have hK : (∑' i, a i * b i) ≤ K := (hsb a ha).tsum_le_of_sum_le ha.2
    rw [hsplit, abs_of_nonneg hnonneg]
    calc _ ≤ ∑' i, a i * b i / n := hle
      _ = (∑' i, a i * b i) / n := tsum_div_const
      _ ≤ K / n := by gcongr
  have hunif : TendstoUniformlyOn (fun n : ℕ => fun a : ι → ℝ => ∑ i ∈ S n, a i * v i)
      (fun a => ∑' i, a i * v i) atTop (budget b K) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (K / ε)
    filter_upwards [Filter.eventually_ge_atTop (N + 1)] with n hn a ha
    have hn0 : 0 < n := by omega
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [Real.dist_eq]
    refine lt_of_le_of_lt (htail n hn0 a ha) ?_
    rw [div_lt_iff₀ hnr]
    have : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ hε] at hN
    nlinarith
  refine hunif.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n => ?_)))
  exact (continuous_finset_sum _ (fun i _ => (continuous_apply i).mul continuous_const)).continuousOn

