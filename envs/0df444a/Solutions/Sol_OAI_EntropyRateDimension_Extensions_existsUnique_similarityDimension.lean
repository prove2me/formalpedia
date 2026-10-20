-- Prove2me | solution 1 for OAI.EntropyRateDimension.Extensions.existsUnique_similarityDimension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:01:36.656372+00:00
-- url     : https://prove2.me/submissions/b439e31b-54f5-4cef-a14d-54f140a7a5df

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/AttractorDimension.lean:L22-L46
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Extensions.existsUnique_similarityDimension. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Model
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Main__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_NoOverlaps
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Attractor
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_AttractorDimension

-- ---- from OAI.MeasureTheory.SelfSimilar.AttractorDimension ----
namespace OAI

universe uι

open scoped BigOperators ENNReal Topology
open MeasureTheory Set Filter

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

theorem similaritySum_strictAnti (S : System ι) : StrictAnti (similaritySum S) := by
  intro a b hab
  exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    (fun i _ => Real.rpow_lt_rpow_of_exponent_gt (S.ratio_pos i) (S.ratio_lt_one i) hab)

/-- Includes the one-symbol boundary: no assumption of at least two symbols. -/
theorem existsUnique_similarityDimension (S : System ι) :
    ∃! s : ℝ, 0 ≤ s ∧ similaritySum S s = 1 := by
  have hcont : Continuous (similaritySum S) :=
    continuous_finsetSum _ (fun i _ => Real.continuous_const_rpow (S.ratio_pos i).ne')
  have hlim : Tendsto (similaritySum S) atTop (𝓝 0) := by
    change Tendsto (fun s : ℝ => ∑ i, |S.ratio i| ^ s) atTop (𝓝 0)
    have hh : Tendsto (fun s : ℝ => ∑ i, |S.ratio i| ^ s) atTop
        (𝓝 (∑ _i : ι, (0 : ℝ))) :=
      tendsto_finsetSum Finset.univ (fun i _ =>
        tendsto_rpow_atTop_of_base_lt_one |S.ratio i|
          (lt_trans (by norm_num : (-1 : ℝ) < 0) (S.ratio_pos i))
          (S.ratio_lt_one i))
    simpa only [Finset.sum_const_zero] using hh
  obtain ⟨b, hb, hb0⟩ :=
    ((hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).and
      (eventually_ge_atTop (0 : ℝ))).exists
  have hzero : 1 ≤ similaritySum S 0 := by
    simpa [similaritySum] using (show (1 : ℝ) ≤ Fintype.card ι by
      exact_mod_cast Fintype.card_pos (α := ι))
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc' hb0 hcont.continuousOn
    (show (1 : ℝ) ∈ Set.Icc (similaritySum S b) (similaritySum S 0) from ⟨hb.le, hzero⟩)
  refine ⟨s, ⟨hs.1, he⟩, ?_⟩
  intro t ht
  exact (similaritySum_strictAnti S).injective (ht.2.trans he.symm)

end EntropyRateDimension.Extensions

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Extensions
open scoped BigOperators ENNReal Topology
open MeasureTheory Set Filter


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.Extensions.existsUnique_similarityDimension.{uι} := @_root_.OAI.EntropyRateDimension.Extensions.existsUnique_similarityDimension.{uι}
