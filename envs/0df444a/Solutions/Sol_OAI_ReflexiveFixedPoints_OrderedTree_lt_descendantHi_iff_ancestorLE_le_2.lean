-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.OrderedTree.lt_descendantHi_iff_ancestorLE_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:39:00.183984+00:00
-- url     : https://prove2.me/submissions/7d223536-b45b-4931-92a9-4fd0da331d5a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/OrderedTreeIntervals.lean:L146-L163
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.OrderedTree.lt_descendantHi_iff_ancestorLE_le. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Nonexpansive_BlockBefore
import Definitions.Def_OAI_Analysis_Nonexpansive_SwitchingStates
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedTreeIntervals
import Theorems.Thm_OAI_ReflexiveFixedPoints_OrderedTree_ancestorLE_eq_iff_interval
import Theorems.Thm_OAI_ReflexiveFixedPoints_OrderedTree_descendantHi_le_descendantLo_of_lt
import Theorems.Thm_OAI_ReflexiveFixedPoints_OrderedTree_lt_descendantLo_iff_ancestorLE_lt

-- ---- from OAI.Analysis.Nonexpansive.OrderedTreeIntervals ----
namespace OAI

/-!
# Consecutive descendant blocks in an ordered tree

The ancestor maps are monotone and surjective. Their nonempty fibers are
intervals. Endpoints are natural numbers, so the upper endpoint may equal
the cardinality of the terminal level.
-/

namespace ReflexiveFixedPoints.OrderedTree

variable (T : OrderedTree) {i j : ℕ}

theorem descendantFirst_le_of_ancestor_eq (h : i ≤ j) (v : T.Node i)
    (s : T.Node j) (hs : T.ancestorLE h s = v) :
    T.descendantFirst h v ≤ s := by
  exact Finset.min'_le (T.descendants h v) s
    ((T.mem_descendants h v s).2 hs)

theorem descendantLo_lt_hi (h : i ≤ j) (v : T.Node i) :
    T.descendantLo h v < T.descendantHi h v := by
  have hle := T.descendantFirst_le_of_ancestor_eq h v
    (T.descendantLast h v) (T.ancestorLE_descendantLast h v)
  exact Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp hle)

/-- Every leaf belongs to its own ancestor's block. -/
theorem self_mem_ancestor_interval (h : i ≤ j) (s : T.Node j) :
    T.descendantLo h (T.ancestorLE h s) ≤ s.val ∧
      s.val < T.descendantHi h (T.ancestorLE h s) :=
  (T.ancestorLE_eq_iff_interval h (T.ancestorLE h s) s).1 rfl

/-- The threshold just after the end of `v`'s block separates exactly the
nodes whose ancestor is at most `v`. -/
theorem lt_descendantHi_iff_ancestorLE_le (h : i ≤ j)
    (v : T.Node i) (s : T.Node j) :
    s.val < T.descendantHi h v ↔ T.ancestorLE h s ≤ v := by
  constructor
  · intro hs
    apply le_of_not_gt
    intro hvs
    have hsep := T.descendantHi_le_descendantLo_of_lt h v
      (T.ancestorLE h s) hvs
    have hown := T.self_mem_ancestor_interval h s
    exact (not_le_of_gt hs) (le_trans hsep hown.1)
  · intro hsv
    rcases eq_or_lt_of_le hsv with heq | hlt
    · exact ((T.ancestorLE_eq_iff_interval h v s).1 heq).2
    · have hlo := (T.lt_descendantLo_iff_ancestorLE_lt h v s).2 hlt
      exact lt_trans hlo (T.descendantLo_lt_hi h v)

end ReflexiveFixedPoints.OrderedTree

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.OrderedTree


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.OrderedTree.lt_descendantHi_iff_ancestorLE_le := @_root_.OAI.ReflexiveFixedPoints.OrderedTree.lt_descendantHi_iff_ancestorLE_le
