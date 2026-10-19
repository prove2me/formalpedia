-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.OrderedTree.descendantHi_le_descendantLo_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:35:02.437417+00:00
-- url     : https://prove2.me/submissions/2a53c764-6335-4d67-bf81-28eb3bca6376

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/OrderedTreeIntervals.lean:L99-L114
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.OrderedTree.descendantHi_le_descendantLo_of_lt. The node keeps its source
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

-- ---- from OAI.Analysis.Nonexpansive.OrderedTree ----
namespace OAI

/-!
# Ordered trees with finite nonempty levels

The parent maps are monotone surjections. Thus every node has children,
and the children of consecutive parents occur in consecutive groups.
Ancestor maps are actual finite composites of parent maps.
-/

namespace ReflexiveFixedPoints

namespace OrderedTree

variable (T : OrderedTree)

theorem ancestorLE_monotone {i j : ℕ} (h : i ≤ j) :
    Monotone (T.ancestorLE h) := by
  induction h using Nat.leRec with
  | refl => simpa using (monotone_id : Monotone (id : T.Node i → T.Node i))
  | @le_succ_of_le j h ih =>
      rw [T.ancestorLE_step h]
      exact ih.comp (T.parent_monotone j)

end OrderedTree
end ReflexiveFixedPoints

end OAI

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

/-- Earlier nodes have descendant blocks entirely before later nodes' blocks. -/
theorem descendantHi_le_descendantLo_of_lt (h : i ≤ j)
    (v w : T.Node i) (hvw : v < w) :
    T.descendantHi h v ≤ T.descendantLo h w := by
  have hlastfirst : T.descendantLast h v < T.descendantFirst h w := by
    apply lt_of_not_ge
    intro hle
    have hwv : w ≤ v := by
      calc
        w = T.ancestorLE h (T.descendantFirst h w) :=
          (T.ancestorLE_descendantFirst h w).symm
        _ ≤ T.ancestorLE h (T.descendantLast h v) :=
          T.ancestorLE_monotone h hle
        _ = v := T.ancestorLE_descendantLast h v
    exact (not_le_of_gt hvw) hwv
  exact Nat.succ_le_of_lt (Fin.lt_def.mp hlastfirst)

end ReflexiveFixedPoints.OrderedTree

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.OrderedTree


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.OrderedTree.descendantHi_le_descendantLo_of_lt := @_root_.OAI.ReflexiveFixedPoints.OrderedTree.descendantHi_le_descendantLo_of_lt
