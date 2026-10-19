-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.dyadic_weighted_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:21:03.477071+00:00
-- url     : https://prove2.me/submissions/2622eb4b-60fd-4946-b554-bacd02cd80f0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/SwitchingScalar.lean:L103-L121
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.dyadic_weighted_tail_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_WeightedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeEvaluation
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeFrontier
import Definitions.Def_OAI_Analysis_Nonexpansive_PredictionCompact
import Definitions.Def_OAI_Analysis_Nonexpansive_PredictionOutputs
import Definitions.Def_OAI_Analysis_Nonexpansive_PrefixPredictionOutputs
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeBudget
import Definitions.Def_OAI_Analysis_Nonexpansive_Resolvents
import Definitions.Def_OAI_Analysis_Nonexpansive_GeneratedMaps
import Definitions.Def_OAI_Analysis_Nonexpansive_TailMaps
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateRecords
import Definitions.Def_OAI_Analysis_Nonexpansive_Diametral
import Definitions.Def_OAI_Analysis_Nonexpansive_CompactDetector
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateThreshold
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidatePreparation
import Definitions.Def_OAI_Analysis_Nonexpansive_SequentialHistory
import Definitions.Def_OAI_Analysis_Nonexpansive_AdaptiveRun
import Definitions.Def_OAI_Analysis_Nonexpansive_AdaptiveConvexPrefix
import Definitions.Def_OAI_Analysis_Nonexpansive_AdaptiveSelection
import Definitions.Def_OAI_Analysis_Nonexpansive_AdaptiveParentReturn
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakSelfMap
import Definitions.Def_OAI_Analysis_Nonexpansive_PointwiseWeakApproximation
import Definitions.Def_OAI_Analysis_Nonexpansive_CompactMapSemigroup
import Definitions.Def_OAI_Analysis_Nonexpansive_TailMapSemigroup
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakNestedConvexHull
import Definitions.Def_OAI_Analysis_Nonexpansive_Anchor
import Definitions.Def_OAI_Analysis_Nonexpansive_AnchorAdaptiveSelection
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateSelection
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedGroupConcat
import Definitions.Def_OAI_Analysis_Nonexpansive_FrontierFromGroups
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLevel
import Definitions.Def_OAI_Analysis_Nonexpansive_FrontierTower
import Definitions.Def_OAI_Analysis_Nonexpansive_TerminalSequence
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateStages
import Definitions.Def_OAI_Analysis_Nonexpansive_GlobalCandidateOrdinals
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLabels
import Definitions.Def_OAI_Analysis_Nonexpansive_ParentReturnHistory
import Definitions.Def_OAI_Analysis_Nonexpansive_FinitePrefixEmbedding
import Definitions.Def_OAI_Analysis_Nonexpansive_ListRunPrefix
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLevelHistory
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLedger
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLedgerJoin
import Definitions.Def_OAI_Analysis_Nonexpansive_PrefixPredictionReindex
import Definitions.Def_OAI_Analysis_Nonexpansive_PredictionCutoff
import Definitions.Def_OAI_Analysis_Nonexpansive_SubtreeEvaluation
import Definitions.Def_OAI_Analysis_Nonexpansive_SubtreeErrors

-- ---- from OAI.Analysis.Nonexpansive.SwitchingScalar ----
namespace OAI

/-!
# Scalar estimates for finite leaf switching

The first estimates telescope the actual scaled ancestor recurrence.  The
second estimates bound a finite dyadic tolerance tail, including an empty
tail.  These lemmas involve only real scalars and finite sums; the switching
construction supplies their hypotheses from its actual maps and weights.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

/-- Exact finite geometric sum for the dyadic tolerance coefficients. -/
theorem dyadic_sum_range (N : ℕ) :
    (∑ d ∈ Finset.range N, (1 / 2 : ℝ) ^ (d + 1)) = 1 - (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [pow_succ]
      ring

/-- Exact finite dyadic tail, including the endpoint term that is discarded
in the later upper bound. -/
theorem dyadic_sum_Ico (k N : ℕ) (hkN : k ≤ N) :
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1)) =
      (1 / 2 : ℝ) ^ k - (1 / 2 : ℝ) ^ N := by
  rw [Finset.sum_Ico_eq_sub _ hkN, dyadic_sum_range, dyadic_sum_range]
  ring

/-- A nonnegative decreasing budget schedule bounds every finite dyadic
tolerance tail.  No infinite series or limiting interchange is used. -/
theorem dyadic_weighted_tail_le (M : ℕ → ℝ)
    (hM_nonneg : ∀ d, 0 ≤ M d) (hM_anti : Antitone M)
    (k N : ℕ) (hkN : k ≤ N) :
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M d) ≤
      (1 / 2 : ℝ) ^ k * M k := by
  calc
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M d) ≤
        ∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M k := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hM_anti (Finset.mem_Ico.mp hd).1)
        (pow_nonneg (by norm_num) _)
    _ = ((1 / 2 : ℝ) ^ k - (1 / 2 : ℝ) ^ N) * M k := by
      rw [← Finset.sum_mul, dyadic_sum_Ico k N hkN]
    _ ≤ (1 / 2 : ℝ) ^ k * M k := by
      apply mul_le_mul_of_nonneg_right _ (hM_nonneg k)
      exact sub_le_self _ (pow_nonneg (by norm_num) _)

end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.dyadic_weighted_tail_le := @_root_.OAI.ReflexiveFixedPoints.dyadic_weighted_tail_le
