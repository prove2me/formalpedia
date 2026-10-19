-- Prove2me | solution 2 for OAI.EntropyRateDimension.BallRatios.ae_logRatio_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:04:14.197268+00:00
-- url     : https://prove2.me/submissions/d4bf9c45-6cbb-421a-b67a-96376f57ef42

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BallRatios.lean:L223-L239
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.BallRatios.ae_logRatio_limit. The node keeps its source
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

theorem ae_logRatio_limit (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) : ∀ᵐ x ∂ν,
      1 ≤ (μ.rnDeriv ν x).toReal ∧
      Tendsto (logRatio μ ν x) (𝓝[>] 0) (𝓝 (Real.log (μ.rnDeriv ν x).toReal)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ ν, μ.rnDeriv_ne_top ν,
    ν.support_mem_ae] with x hlim htop hx
  have hge : 1 ≤ μ.rnDeriv ν x := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have hp := (Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr)
    apply (ENNReal.le_div_iff_mul_le (Or.inl hp.ne') (Or.inl (measure_ne_top ν _))).mpr
    simpa only [one_mul] using hν (closedBall x r)
  have hreal : 1 ≤ (μ.rnDeriv ν x).toReal := by
    simpa using ENNReal.toReal_mono htop hge
  refine ⟨hreal,?_⟩
  exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one hreal))).tendsto.comp
    ((ENNReal.continuousAt_toReal htop).tendsto.comp hlim)

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


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.BallRatios.ae_logRatio_limit := @_root_.OAI.EntropyRateDimension.BallRatios.ae_logRatio_limit
