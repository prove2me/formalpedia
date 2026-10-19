-- Prove2me | solution 1 for OAI.EntropyRateDimension.System.average_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:58:01.675598+00:00
-- url     : https://prove2.me/submissions/3915971f-e04d-45e3-9866-acd7a7511908

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uι
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι]


theorem solution (S : System ι) {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) (n : ℕ) (x : ℝ) : |S.average f n x| ≤ C := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
    simp only [System.average]
    calc |∑ i, S.weight i * S.average f n (S.affine i x)|
        ≤ ∑ i, |S.weight i * S.average f n (S.affine i x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, S.weight i * C := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul, abs_of_pos (S.weight_pos i)]
          exact mul_le_mul_of_nonneg_left (ih _) (S.weight_pos i).le
      _ = C := by rw [← Finset.sum_mul, S.weight_sum, one_mul]

