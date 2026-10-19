-- Prove2me | solution 1 for OAI.EntropyRateDimension.BallRatios.information_one_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:05:09.568072+00:00
-- url     : https://prove2.me/submissions/9e1645f6-a427-4d8d-8613-05e16453465d

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.BallRatios
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators


theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hK : IsCompact μ.support) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ μ.support, information μ x 1 ≤ C := by
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun y => Metric.ball y (1/2))
    (fun y _ => Metric.ball_mem_nhds y (by norm_num))
  refine ⟨∑ y ∈ t, |Real.log (μ.real (Metric.ball y (1/2)))|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (hcov hx)
  have hpos : 0 < μ.real (Metric.ball y (1/2)) := by
    have h0 := (Measure.mem_support_iff_forall y).mp (htK y hyt) _
      (Metric.ball_mem_nhds y (by norm_num : (0:ℝ) < 1/2))
    exact ENNReal.toReal_pos h0.ne' (measure_ne_top _ _)
  have hsub : Metric.ball y (1/2) ⊆ Metric.closedBall x 1 := by
    intro z hz
    rw [Metric.mem_ball] at hz hxy
    rw [Metric.mem_closedBall]
    linarith [dist_triangle z y x, dist_comm x y]
  unfold information
  calc -Real.log (μ.real (closedBall x 1)) ≤ -Real.log (μ.real (Metric.ball y (1/2))) :=
        neg_le_neg (Real.log_le_log hpos (measureReal_mono hsub))
    _ ≤ |Real.log (μ.real (Metric.ball y (1/2)))| := neg_le_abs _
    _ ≤ _ := Finset.single_le_sum (f := fun y => |Real.log (μ.real (Metric.ball y (1/2)))|)
        (fun _ _ => abs_nonneg _) hyt

