-- Prove2me | solution 2 for OAI.EntropyRateDimension.LocalMass.eventual_lower_of_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:09:17.0587+00:00
-- url     : https://prove2.me/submissions/90cb8c82-4b4b-43fa-9266-fc1d06cf06c9

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/LocalMass.lean:L117-L136
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.LocalMass.eventual_lower_of_limit. The node keeps its source
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

-- ---- from OAI.MeasureTheory.SelfSimilar.LocalMass ----
namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace EntropyRateDimension
namespace LocalMass

theorem eventual_lower_of_limit (μ : Measure ℝ) [IsFiniteMeasure μ] {x e d : ℝ}
    (hx : x ∈ μ.support) (hde : d < e)
    (hlim : Tendsto (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r) := by
  have hev := hlim.eventually (gt_mem_nhds hde)
  obtain ⟨R,hR,hRx⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨min R 1,lt_min hR zero_lt_one,?_⟩
  intro r hr hrR
  have hr1 : r < 1 := lt_of_lt_of_le hrR (min_le_right _ _)
  have harr : -Real.log (μ.real (closedBall x r)) / -Real.log r < e :=
    hRx ⟨by simpa [Real.dist_eq,abs_of_pos hr] using lt_of_lt_of_le hrR (min_le_left _ _),hr⟩
  have hh := (div_lt_iff₀ (neg_pos.mpr (Real.log_neg hr hr1))).mp harr
  have hmass : 0 < μ.real (closedBall x r) :=
    ENNReal.toReal_pos (ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _
      (closedBall_mem_nhds x hr))) (measure_ne_top μ _)
  rw [Real.rpow_def_of_pos hr,← Real.exp_log hmass]
  apply Real.exp_le_exp.mpr
  nlinarith

end LocalMass
end EntropyRateDimension

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.LocalMass
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.LocalMass.eventual_lower_of_limit := @_root_.OAI.EntropyRateDimension.LocalMass.eventual_lower_of_limit
