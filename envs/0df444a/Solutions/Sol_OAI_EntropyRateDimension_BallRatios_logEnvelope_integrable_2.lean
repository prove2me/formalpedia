-- Prove2me | solution 2 for OAI.EntropyRateDimension.BallRatios.logEnvelope_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:00:57.946796+00:00
-- url     : https://prove2.me/submissions/24ab4d90-7295-44a4-a5ca-63c0f5445b55

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BallRatios.lean:L150-L167
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.BallRatios.logEnvelope_integrable. The node keeps its source
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

theorem measurable_ball_mass (μ : Measure ℝ) [SFinite μ] (r : ℝ) :
    Measurable (fun x : ℝ => μ (closedBall x r)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | dist p.2 p.1 ≤ r} :=
    measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  exact measurable_measure_prodMk_left hs

theorem maximal_measurable (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measurable (maximal μ ν) := by
  apply Measurable.iSup
  intro q
  exact (measurable_ball_mass μ _).div (measurable_ball_mass ν _)

theorem logEnvelope_nonneg (μ ν : Measure ℝ) (x : ℝ) : 0 ≤ logEnvelope μ ν x :=
  le_max_left _ _

theorem logEnvelope_measurable (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measurable (logEnvelope μ ν) :=
  measurable_const.max (maximal_measurable μ ν).ennreal_toReal.log

theorem logEnvelope_tail {N : ℕ}
    (hN : ∀ (μ ν : Measure ℝ) (t : ℝ≥0∞) (E : Set ℝ),
      (∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ν (closedBall x r) ≤ t*μ (closedBall x r)) →
      ν E ≤ N*t*μ univ)
    (μ ν : Measure ℝ) [IsFiniteMeasure ν] {t : ℝ} (ht : 0 ≤ t) :
    ν {x | t < logEnvelope μ ν x} ≤
      (N : ℝ≥0∞)*μ univ*ENNReal.ofReal (Real.exp (-t)) := by
  calc
    _ ≤ ν {x | ENNReal.ofReal (Real.exp t) < maximal μ ν x} := by
      apply measure_mono
      intro x hx
      have hh : t < Real.log (maximal μ ν x).toReal :=
        (lt_max_iff.mp hx).resolve_left (not_lt_of_ge ht)
      have hp : 0 < (maximal μ ν x).toReal := by
        apply lt_of_le_of_ne ENNReal.toReal_nonneg
        intro he
        simp [← he] at hh
        linarith
      have he := (Real.lt_log_iff_exp_lt hp).mp hh
      exact ((ENNReal.ofReal_lt_ofReal_iff hp).mpr he).trans_le ENNReal.ofReal_toReal_le
    _ ≤ (N : ℝ≥0∞)*(ENNReal.ofReal (Real.exp t))⁻¹*μ univ :=
      maximal_tail hN μ ν _ (by simp [Real.exp_pos]) (by simp)
    _ = _ := by rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos t)]; ring

theorem logEnvelope_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (logEnvelope μ ν) ν := by
  obtain ⟨N,hN⟩ := exists_small_ratio_bound
  refine ⟨(logEnvelope_measurable μ ν).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (logEnvelope_nonneg μ ν)),
    lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall (logEnvelope_nonneg μ ν))
      (logEnvelope_measurable μ ν).aemeasurable]
  calc
    _ ≤ ∫⁻ t : ℝ in Ioi 0, (N : ℝ≥0∞)*μ univ*ENNReal.ofReal (Real.exp (-t)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact logEnvelope_tail hN μ ν ht.le
    _ = (N : ℝ≥0∞)*μ univ*∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-t)) :=
      lintegral_const_mul _ (by fun_prop)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (measure_lt_top μ _))
      ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall
        (fun t : ℝ => (Real.exp_pos (-t)).le))).mp
          (integrableOn_exp_neg_Ioi 0).hasFiniteIntegral)

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


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.BallRatios.logEnvelope_integrable := @_root_.OAI.EntropyRateDimension.BallRatios.logEnvelope_integrable
