-- Prove2me | solution 2 for OAI.EntropyRateDimension.System.average_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:53:08.479017+00:00
-- url     : https://prove2.me/submissions/f3b14249-00bb-4ad0-b98f-467fac9836e1

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/InvariantLaw.lean:L30-L42
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.System.average_bound. The node keeps its source
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

-- ---- from OAI.MeasureTheory.SelfSimilar.InvariantLaw ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
namespace EntropyRateDimension.System
open MeasureTheory Filter Set
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι]

theorem average_bound (S : System ι) {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) (n : ℕ) (x : ℝ) : |S.average f n x| ≤ C := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
    calc
      _ ≤ ∑ i, |S.weight i * S.average f n (S.affine i x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, S.weight i * C := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul,abs_of_nonneg (S.weight_nonneg i)]
        exact mul_le_mul_of_nonneg_left (ih _) (S.weight_nonneg i)
      _ = C := by rw [← Finset.sum_mul,S.weight_sum,one_mul]

variable [Nonempty ι]

end EntropyRateDimension.System

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.System.average_bound.{uι} := @_root_.OAI.EntropyRateDimension.System.average_bound.{uι}
