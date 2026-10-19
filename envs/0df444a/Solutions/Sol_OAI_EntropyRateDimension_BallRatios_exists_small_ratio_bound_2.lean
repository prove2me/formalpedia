-- Prove2me | solution 2 for OAI.EntropyRateDimension.BallRatios.exists_small_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:57:22.992986+00:00
-- url     : https://prove2.me/submissions/9f10ecd2-fe62-473f-b604-7dcea607debf

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BallRatios.lean:L18-L55
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.BallRatios.exists_small_ratio_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.MeasureTheory.SelfSimilar.BallRatios ----
namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace EntropyRateDimension
namespace BallRatios

theorem exists_small_ratio_bound : ∃ N : ℕ, ∀ (μ ν : Measure ℝ) (t : ℝ≥0∞)
    (E : Set ℝ),
    (∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ν (closedBall x r) ≤ t*μ (closedBall x r)) →
    ν E ≤ N*t*μ univ := by
  classical
  obtain ⟨N,τ,hτ,hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := ℝ)
  refine ⟨N, ?_⟩
  intro μ ν t E hE
  choose r hr hr1 hrat using fun x : E => hE x.val x.property
  let q : Besicovitch.BallPackage E ℝ :=
    { c := Subtype.val, r := r, rpos := hr, r_bound := 1, r_le := hr1 }
  obtain ⟨s,hd,hcover⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
  have hcnt : ∀ i, (s i).Countable := by
    intro i
    apply (hd i).countable_of_nonempty_interior
    intro x hx
    exact ⟨x.val, ball_subset_interior_closedBall (mem_ball_self (hr x))⟩
  have hb : ∀ i, ν (⋃ x ∈ s i, ball (q.c x) (q.r x)) ≤ t*μ univ := by
    intro i
    calc
      _ ≤ ∑' x : s i, ν (closedBall (q.c x.val) (q.r x.val)) := by
        apply le_trans (measure_biUnion_le ν (hcnt i) _)
        exact ENNReal.tsum_le_tsum fun x => measure_mono ball_subset_closedBall
      _ ≤ ∑' x : s i, t*μ (closedBall (q.c x.val) (q.r x.val)) :=
        ENNReal.tsum_le_tsum fun x => hrat x.val
      _ = t * μ (⋃ x ∈ s i, closedBall (q.c x) (q.r x)) := by
        rw [ENNReal.tsum_mul_left, measure_biUnion (hcnt i) (hd i)
          (fun _ _ => measurableSet_closedBall)]
      _ ≤ t*μ univ := mul_le_mul' le_rfl (measure_mono (subset_univ _))
  calc
    ν E ≤ ν (⋃ i, ⋃ x ∈ s i, ball (q.c x) (q.r x)) := by
      apply measure_mono
      intro x hx
      exact hcover ⟨⟨x,hx⟩,rfl⟩
    _ ≤ ∑ i : Fin N, ν (⋃ x ∈ s i, ball (q.c x) (q.r x)) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin N, t*μ univ := Finset.sum_le_sum fun i _ => hb i
    _ = N*t*μ univ := by simp [mul_assoc]

end BallRatios
end EntropyRateDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.BallRatios
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.BallRatios.exists_small_ratio_bound := @_root_.OAI.EntropyRateDimension.BallRatios.exists_small_ratio_bound
