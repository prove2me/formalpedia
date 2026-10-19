-- Prove2me | solution 2 for OAI.EntropyRateDimension.System.ratio_wordType
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:41:57.089695+00:00
-- url     : https://prove2.me/submissions/ba4503cf-3b88-4e2a-9839-8105447e215c

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BlockWords.lean:L119-L134
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.System.ratio_wordType. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords

-- ---- from OAI.MeasureTheory.SelfSimilar.BlockWords ----
namespace OAI

universe uι uα uβ uγ

namespace EntropyRateDimension.FiniteEntropy
open scoped BigOperators

end EntropyRateDimension.FiniteEntropy

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem ratio_wordType (S : System ι) {b : ℕ} (hb : 0 < b) (w v : Fin b → ι)
    (h : wordType w=wordType v) : (S.blocks hb).ratio w=(S.blocks hb).ratio v := by
  classical
  have ht (u : Fin b → ι) : (S.completeMap u).1=∏ i, S.ratio i^(wordType u i).val := by
    rw [S.completeMap_slope,← Finset.prod_fiberwise Finset.univ u]
    apply Finset.prod_congr rfl
    intro i _
    calc
      ∏ j ∈ Finset.univ.filter (fun j => u j=i), S.ratio (u j) =
          ∏ _j ∈ Finset.univ.filter (fun j => u j=i), S.ratio i := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [(Finset.mem_filter.mp hj).2]
      _ = _ := by simp only [Finset.prod_const,wordType]
  change (S.completeMap w).1=(S.completeMap v).1
  rw [ht,ht,h]

end EntropyRateDimension.System

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.System.ratio_wordType.{uι} := @_root_.OAI.EntropyRateDimension.System.ratio_wordType.{uι}
