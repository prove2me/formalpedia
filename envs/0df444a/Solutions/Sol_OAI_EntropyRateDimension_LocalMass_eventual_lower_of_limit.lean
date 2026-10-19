-- Prove2me | solution 1 for OAI.EntropyRateDimension.LocalMass.eventual_lower_of_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:59:33.048281+00:00
-- url     : https://prove2.me/submissions/f2a7427c-dc01-4a71-815f-3a3ea9e0093f

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

open OAI OAI.EntropyRateDimension
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal


theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] {x e d : ℝ}
    (hx : x ∈ μ.support) (hde : d < e)
    (hlim : Tendsto (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r) := by
  have hev := hlim.eventually (eventually_lt_nhds hde)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, h⟩ := hev
  refine ⟨min ε 1, lt_min hε one_pos, fun r hr hrR => ?_⟩
  have hrε : dist r 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hr]
    exact lt_of_lt_of_le hrR (min_le_left _ _)
  have h1 := h hrε (Set.mem_Ioi.mpr hr)
  have hlogr : 0 < -Real.log r :=
    neg_pos.mpr (Real.log_neg hr (lt_of_lt_of_le hrR (min_le_right _ _)))
  have hpos : 0 < μ.real (closedBall x r) := by
    have h0 := (Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr)
    exact ENNReal.toReal_pos h0.ne' (measure_ne_top _ _)
  rw [div_lt_iff₀ hlogr] at h1
  have h2 : Real.log (r^e) < Real.log (μ.real (closedBall x r)) := by
    rw [Real.log_rpow hr]; linarith
  exact ((Real.log_lt_log_iff (by positivity) hpos).mp h2).le

