-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.dyadic_weighted_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:55:36.997986+00:00
-- url     : https://prove2.me/submissions/0c1c559b-9246-4b7d-bf53-f6b0a82345d1

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

open OAI OAI.ReflexiveFixedPoints
open scoped BigOperators
theorem rfp_dyadic (M : ℕ → ℝ)
    (hM_nonneg : ∀ d, 0 ≤ M d) (hM_anti : Antitone M)
    (k : ℕ) : ∀ n : ℕ,
    (∑ d ∈ Finset.Ico k (k + n), (1 / 2 : ℝ) ^ (d + 1) * M d) ≤
      ((1 / 2 : ℝ) ^ k - (1 / 2 : ℝ) ^ (k + n)) * M k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have h1 : M (k + n) ≤ M k := hM_anti (by omega)
    have h2 : (0 : ℝ) ≤ (1 / 2) ^ (k + n + 1) := by positivity
    have h3 : (1 / 2 : ℝ) ^ (k + n + 1) * M (k + n) ≤ (1 / 2 : ℝ) ^ (k + n + 1) * M k :=
      mul_le_mul_of_nonneg_left h1 h2
    have h4 : (1 / 2 : ℝ) ^ (k + n) = 2 * (1 / 2 : ℝ) ^ (k + n + 1) := by
      rw [pow_succ]; ring
    have e1 : ((1 / 2 : ℝ) ^ k - (1 / 2 : ℝ) ^ (k + n)) * M k =
        (1 / 2 : ℝ) ^ k * M k - 2 * ((1 / 2 : ℝ) ^ (k + n + 1) * M k) := by rw [h4]; ring
    have e2 : ((1 / 2 : ℝ) ^ k - (1 / 2 : ℝ) ^ (k + n + 1)) * M k =
        (1 / 2 : ℝ) ^ k * M k - (1 / 2 : ℝ) ^ (k + n + 1) * M k := by ring
    rw [e1] at ih; rw [e2]
    have h5 : 0 ≤ (1 / 2 : ℝ) ^ (k + n + 1) * M k := mul_nonneg h2 (hM_nonneg k)
    linarith

theorem solution (M : ℕ → ℝ)
    (hM_nonneg : ∀ d, 0 ≤ M d) (hM_anti : Antitone M)
    (k N : ℕ) (hkN : k ≤ N) :
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M d) ≤
      (1 / 2 : ℝ) ^ k * M k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkN
  refine (rfp_dyadic M hM_nonneg hM_anti k n).trans ?_
  have : (0 : ℝ) ≤ (1 / 2) ^ (k + n) := by positivity
  nlinarith [hM_nonneg k]
