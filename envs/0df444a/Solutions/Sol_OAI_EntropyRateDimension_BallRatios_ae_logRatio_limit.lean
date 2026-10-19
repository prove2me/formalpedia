-- Prove2me | solution 1 for OAI.EntropyRateDimension.BallRatios.ae_logRatio_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:09:15.36899+00:00
-- url     : https://prove2.me/submissions/25bfe773-c288-4dc8-b823-8d0160fd8a81

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


theorem solution (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) : ∀ᵐ x ∂ν,
      1 ≤ (μ.rnDeriv ν x).toReal ∧
      Tendsto (logRatio μ ν x) (𝓝[>] 0) (𝓝 (Real.log (μ.rnDeriv ν x).toReal)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ ν, Measure.rnDeriv_lt_top μ ν,
    (Measure.support_mem_ae : ν.support ∈ ae ν)] with x hx htop hsupp
  have hge : 1 ≤ μ.rnDeriv ν x := by
    apply ge_of_tendsto hx
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hpos : 0 < ν (closedBall x r) :=
      (Measure.mem_support_iff_forall x).mp hsupp _ (closedBall_mem_nhds x hr)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl (measure_ne_top _ _)), one_mul]
    exact Measure.le_iff'.1 hν _
  have h1 : 1 ≤ (μ.rnDeriv ν x).toReal := by simpa using ENNReal.toReal_mono htop.ne hge
  refine ⟨h1, ?_⟩
  exact ((ENNReal.tendsto_toReal htop.ne).comp hx).log (ne_of_gt (lt_of_lt_of_le one_pos h1))

