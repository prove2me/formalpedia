-- Prove2me | solution 1 for OAI.EntropyRateDimension.Windows.sum_target_shift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:24:28.588519+00:00
-- url     : https://prove2.me/submissions/3dbbaac7-846f-493c-a6e4-a735fa791ece

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Windows
open scoped BigOperators


theorem solution (f : ℤ → ℝ) (a B c T : ℤ)
    (ha : 1 ≤ a) (hc : 0 ≤ c) (hB : B+c ≤ T) :
    (∑ L ∈ Finset.Icc 1 T, if a ≤ L-c ∧ L-c ≤ B then f (L-c) else 0)=
      ∑ ℓ ∈ Finset.Icc a B, f ℓ := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun L => L - c) (fun ℓ => ℓ + c)
  · intro L hL
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hL ⊢
    exact hL.2
  · intro ℓ hℓ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hℓ ⊢
    refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · intro L _; simp
  · intro ℓ _; simp
  · intro L _; rfl

