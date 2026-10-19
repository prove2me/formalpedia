-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.OrderedTree.ancestorLE_eq_iff_interval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:33:02.109739+00:00
-- url     : https://prove2.me/submissions/60be4e32-951a-4100-875d-163f45e3a9e8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/OrderedTreeIntervals.lean:L58-L83
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.OrderedTree.ancestorLE_eq_iff_interval. The node keeps its source
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

theorem descendantFirst_le_of_ancestor_eq (h : i ≤ j) (v : T.Node i)
    (s : T.Node j) (hs : T.ancestorLE h s = v) :
    T.descendantFirst h v ≤ s := by
  exact Finset.min'_le (T.descendants h v) s
    ((T.mem_descendants h v s).2 hs)

theorem le_descendantLast_of_ancestor_eq (h : i ≤ j) (v : T.Node i)
    (s : T.Node j) (hs : T.ancestorLE h s = v) :
    s ≤ T.descendantLast h v := by
  exact Finset.le_max' (T.descendants h v) s
    ((T.mem_descendants h v s).2 hs)

/-- An ancestor fiber is exactly the natural half-open interval between its
first descendant and one past its last descendant. -/
theorem ancestorLE_eq_iff_interval (h : i ≤ j) (v : T.Node i) (s : T.Node j) :
    T.ancestorLE h s = v ↔
      T.descendantLo h v ≤ s.val ∧ s.val < T.descendantHi h v := by
  constructor
  · intro hs
    constructor
    · exact Fin.le_iff_val_le_val.mp
        (T.descendantFirst_le_of_ancestor_eq h v s hs)
    · exact Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp
        (T.le_descendantLast_of_ancestor_eq h v s hs))
  · rintro ⟨hlo, hhi⟩
    have hfirst : T.descendantFirst h v ≤ s :=
      Fin.le_iff_val_le_val.mpr hlo
    have hlast : s ≤ T.descendantLast h v :=
      Fin.le_iff_val_le_val.mpr (Nat.lt_succ_iff.mp hhi)
    apply le_antisymm
    · calc
        T.ancestorLE h s ≤ T.ancestorLE h (T.descendantLast h v) :=
          T.ancestorLE_monotone h hlast
        _ = v := T.ancestorLE_descendantLast h v
    · calc
        v = T.ancestorLE h (T.descendantFirst h v) :=
          (T.ancestorLE_descendantFirst h v).symm
        _ ≤ T.ancestorLE h s := T.ancestorLE_monotone h hfirst

end ReflexiveFixedPoints.OrderedTree

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.OrderedTree


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.OrderedTree.ancestorLE_eq_iff_interval := @_root_.OAI.ReflexiveFixedPoints.OrderedTree.ancestorLE_eq_iff_interval
