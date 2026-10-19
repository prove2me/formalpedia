-- Prove2me | solution 1 for OAI.EntropyRateDimension.System.wordAverage_segment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:01:25.583794+00:00
-- url     : https://prove2.me/submissions/0bc1e9c5-6571-4562-89ba-506e0e45546e

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uι uα
open scoped BigOperators
variable {α : Type uα} [Fintype α]
theorem h41n_sum_append {α : Type*} [Fintype α] {a b : ℕ} (g : (Fin (a+b) → α) → ℝ) :
    ∑ W, g W = ∑ x : Fin a → α, ∑ y : Fin b → α, g (Fin.append x y) := by
  rw [← (Fin.appendEquiv a b).sum_comp, Fintype.sum_prod_type]
  rfl

theorem solution (S : System α) {H j n : ℕ} (hH : j+n ≤ H) (f : List α → ℝ) :
    S.wordAverage H (fun W => f ((W.drop j).take n))=S.wordAverage n f := by
  obtain ⟨r, rfl⟩ : ∃ r, H = j + n + r := ⟨H - (j+n), by omega⟩
  have hww : ∀ {a b : ℕ} (x : Fin a → α) (y : Fin b → α),
      S.wordWeight (Fin.append x y) = S.wordWeight x * S.wordWeight y := by
    intro a b x y
    simp only [System.wordWeight]
    rw [Fin.prod_univ_add]
    simp [Fin.append_left, Fin.append_right]
  have hl : ∀ (a : Fin j → α) (b : Fin n → α) (c : Fin r → α),
      ((List.ofFn a ++ List.ofFn b ++ List.ofFn c).drop j).take n = List.ofFn b := by
    intro a b c
    rw [List.append_assoc, List.drop_left' (by simp), List.take_left' (by simp)]
  unfold System.wordAverage
  rw [h41n_sum_append]
  rw [h41n_sum_append]
  simp only [hww, List.ofFn_fin_append, hl]
  trans ∑ a : Fin j → α, ∑ b : Fin n → α, S.wordWeight a * (S.wordWeight b * f (List.ofFn b))
  · apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
    rw [show S.wordWeight a * (S.wordWeight b * f (List.ofFn b)) = (∑ c : Fin r → α, S.wordWeight c) *
      (S.wordWeight a * (S.wordWeight b * f (List.ofFn b))) by rw [S.wordWeight_sum, one_mul],
      Finset.sum_mul]
    apply Finset.sum_congr rfl; intro c _; ring
  · simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, S.wordWeight_sum, one_mul]

