-- Prove2me | solution 2 for OAI.EntropyRateDimension.BallRatios.logRatio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:02:25.724829+00:00
-- url     : https://prove2.me/submissions/ba3d38ca-ddf2-4416-b69a-d4ee1d8a0be5

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BallRatios.lean:L206-L221
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.BallRatios.logRatio_bounds. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_BallRatios_exists_small_ratio_bound
import Theorems.Thm_OAI_EntropyRateDimension_BallRatios_maximal_tail

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

theorem maximal_finite_ae (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∀ᵐ x ∂ν, maximal μ ν x ≠ ⊤ := by
  obtain ⟨N,hN⟩ := exists_small_ratio_bound
  apply ae_iff.mpr
  simp only [not_not]
  apply le_antisymm _ bot_le
  have hlim : Tendsto (fun n : ℕ => (N : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ * μ univ)
      atTop (𝓝 0) := by
    have hh := ENNReal.Tendsto.const_mul ENNReal.tendsto_nat_nhds_top.inv
      (Or.inr (show (N : ℝ≥0∞) ≠ ⊤ by simp))
    have hf := ENNReal.Tendsto.mul_const hh (Or.inr (measure_ne_top μ univ))
    simpa using hf
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  calc
    ν {x | maximal μ ν x = ⊤} ≤ ν {x | (n : ℝ≥0∞) < maximal μ ν x} := by
      apply measure_mono
      intro x (hx : maximal μ ν x = ⊤)
      change (n : ℝ≥0∞) < maximal μ ν x
      rw [hx]
      exact ENNReal.natCast_lt_top n
    _ ≤ _ := maximal_tail hN μ ν n (by exact_mod_cast hn.ne') (by simp)

theorem tendsto_ball_mass_right (μ : Measure ℝ) [IsFiniteMeasure μ] (x r : ℝ) :
    Tendsto (fun t => μ (closedBall x t)) (𝓝[>] r) (𝓝 (μ (closedBall x r))) := by
  have h := tendsto_measure_biInter_gt (μ := μ) (a := r)
    (s := fun t : ℝ => closedBall x t)
    (fun _ _ => measurableSet_closedBall.nullMeasurableSet)
    (fun _ _ _ h => closedBall_subset_closedBall h)
    ⟨r+1,by linarith,measure_ne_top μ _⟩
  simpa only [biInter_gt_closedBall,Function.comp_def] using h

theorem ratio_le_maximal (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (x : ℝ) (hx : x ∈ ν.support) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    μ (closedBall x r) / ν (closedBall x r) ≤ maximal μ ν x := by
  obtain ⟨q,_hq,hqr,hql⟩ := (Rat.denseRange_cast (𝕜 := ℝ)).exists_seq_strictAnti_tendsto_of_lt
    Rat.cast_strictMono.monotone hr1
  have ht : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[>] r) :=
    tendsto_nhdsWithin_iff.mpr ⟨hql,Eventually.of_forall fun n => (hqr n).1⟩
  have hp : ν (closedBall x r) ≠ 0 :=
    ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr))
  have hlim := ENNReal.Tendsto.div ((tendsto_ball_mass_right μ x r).comp ht)
    (Or.inr hp) ((tendsto_ball_mass_right ν x r).comp ht) (Or.inl (measure_ne_top ν _))
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun n =>
    le_iSup (fun q : Radius => μ (closedBall x (q.val : ℝ)) / ν (closedBall x (q.val : ℝ)))
      ⟨q n,lt_trans hr (hqr n).1,(hqr n).2.le⟩

theorem logRatio_bounds (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) : ∀ᵐ x ∂ν, ∀ r : ℝ, 0 < r → r < 1 →
      0 ≤ logRatio μ ν x r ∧ logRatio μ ν x r ≤ logEnvelope μ ν x := by
  filter_upwards [ν.support_mem_ae,maximal_finite_ae μ ν] with x hx hmax
  intro r hr hr1
  have hp := (Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr)
  have hge : 1 ≤ μ (closedBall x r) / ν (closedBall x r) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hp.ne') (Or.inl (measure_ne_top ν _))).mpr
    simpa only [one_mul] using hν (closedBall x r)
  have htop := ne_top_of_le_ne_top hmax (ratio_le_maximal μ ν x hx hr hr1)
  have hreal : 1 ≤ (μ (closedBall x r) / ν (closedBall x r)).toReal := by
    exact_mod_cast (ENNReal.toReal_mono htop hge)
  refine ⟨Real.log_nonneg hreal,?_⟩
  apply le_trans _ (le_max_right 0 _)
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one hreal)
  exact ENNReal.toReal_mono hmax (ratio_le_maximal μ ν x hx hr hr1)

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


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.BallRatios.logRatio_bounds := @_root_.OAI.EntropyRateDimension.BallRatios.logRatio_bounds
