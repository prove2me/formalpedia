-- Prove2me | solution 1 for OAI.EntropyRateDimension.BallRatios.information_component
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:07:38.871342+00:00
-- url     : https://prove2.me/submissions/34f4ebf1-01e3-4eab-b86d-b369fc7190f8

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.BallRatios
universe uι
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators


theorem solution {ι : Type uι} [Fintype ι] (S : System ι)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : S.SelfSimilar μ) (i : ι)
    {x r : ℝ} (hx : x ∈ μ.support) (hr : 0 < r) :
    information μ (S.affine i x) (|S.ratio i| *r) =
      information μ x r - Real.log (S.weight i) -
        logRatio μ (S.component μ i) (S.affine i x) (|S.ratio i| *r) := by
  have hri : 0 < |S.ratio i| := S.ratio_pos i
  have hw : 0 < S.weight i := S.weight_pos i
  set B' := closedBall (S.affine i x) (|S.ratio i| * r) with hB'_def
  have hpre : S.affine i ⁻¹' B' = closedBall x r := by
    ext y
    simp only [hB'_def, Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq, System.affine]
    rw [show S.ratio i * y + S.offset i - (S.ratio i * x + S.offset i) = S.ratio i * (y - x) by ring,
      abs_mul]
    exact ⟨fun h => le_of_mul_le_mul_left h hri, fun h => mul_le_mul_of_nonneg_left h hri.le⟩
  have haff : Measurable (S.affine i) := by unfold System.affine; fun_prop
  have hcomp : S.component μ i B' = ENNReal.ofReal (S.weight i) * μ (closedBall x r) := by
    simp only [System.component]
    rw [Measure.smul_apply, Measure.map_apply haff measurableSet_closedBall, hpre, smul_eq_mul]
  have hB : 0 < μ (closedBall x r) :=
    (Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr)
  have hge : ENNReal.ofReal (S.weight i) * μ (closedBall x r) ≤ μ B' := by
    rw [← hcomp]
    conv_rhs => rw [hμ]
    rw [Measure.coe_finset_sum, Finset.sum_apply]
    exact Finset.single_le_sum (f := fun j => S.component μ j B') (fun _ _ => bot_le)
      (Finset.mem_univ i)
  have ha : 0 < (μ (closedBall x r)).toReal := ENNReal.toReal_pos hB.ne' (measure_ne_top _ _)
  have hb : 0 < (μ B').toReal := by
    apply ENNReal.toReal_pos _ (measure_ne_top _ _)
    apply ne_of_gt
    exact lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hw).ne' hB.ne') hge
  unfold information logRatio
  rw [hcomp, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal hw.le,
    measureReal_def, measureReal_def]
  rw [Real.log_div hb.ne' (mul_pos hw ha).ne', Real.log_mul hw.ne' ha.ne']
  ring

