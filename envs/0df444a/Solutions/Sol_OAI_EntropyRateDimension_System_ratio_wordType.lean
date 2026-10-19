-- Prove2me | solution 1 for OAI.EntropyRateDimension.System.ratio_wordType
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:26:09.585244+00:00
-- url     : https://prove2.me/submissions/d858bf5e-7264-44ba-a67d-89b182bf9a96

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uι uα uβ uγ
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System in
theorem hn2_prod_wordType {ι : Type*} [Fintype ι] (S : System ι) {b : ℕ} (w : Fin b → ι) :
    ∏ j, S.ratio (w j) = ∏ i, S.ratio i ^ ((wordType w i : Fin (b+1)) : ℕ) := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := w)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]), Finset.prod_const]
  simp only [wordType]

theorem solution (S : System ι) {b : ℕ} (hb : 0 < b) (w v : Fin b → ι)
    (h : wordType w=wordType v) : (S.blocks hb).ratio w=(S.blocks hb).ratio v := by
  show (S.completeMap w).1 = (S.completeMap v).1
  rw [completeMap_slope, completeMap_slope, hn2_prod_wordType, hn2_prod_wordType, h]

