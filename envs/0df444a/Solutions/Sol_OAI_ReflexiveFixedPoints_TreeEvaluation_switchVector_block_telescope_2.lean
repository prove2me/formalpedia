-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.switchVector_block_telescope
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:46:35.413599+00:00
-- url     : https://prove2.me/submissions/a7b8181d-70fb-4bf6-88e3-a4960e56572a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/SwitchingBlocks.lean:L97-L115
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.switchVector_block_telescope. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Nonexpansive_SwitchingBlocks
import Theorems.Thm_OAI_ReflexiveFixedPoints_OrderedTree_sum_descendants_eq_Ico

-- ---- from OAI.Analysis.Nonexpansive.WeightedTree ----
namespace OAI

/-!
# Positive edge weights and the actual path mass

Path mass is defined recursively from the parent maps and edge weights.
Its normalization and its mass on every descendant block are consequences
of the normalization at each parent.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

namespace WeightedTree

variable {T : OrderedTree} (W : WeightedTree T)

theorem pathWeight_pos (k : ℕ) (v : T.Node k) : 0 < W.pathWeight k v := by
  induction k with
  | zero => exact zero_lt_one
  | succ k ih => exact mul_pos (ih (T.parent k v)) (W.weight_pos k v)

end WeightedTree
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.SwitchingStates ----
namespace OAI

/-!
# Actual root states during right-to-left switching

At cutoff `t`, the leaves with index strictly below `t` retain their labels;
all other leaves have the common terminal value.  Decreasing `t` by one is one
actual switch.  Every increment below is a difference of these evaluated root
states, so finite telescoping never assumes that a node map is linear.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints
namespace TreeEvaluation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Consecutive actual root outputs telescope over a half-open interval.
No node map is moved through the sum. -/
theorem switchRoot_interval_telescope (N : ℕ) (y : T.Node N → K) (b : K)
    {lo hi : ℕ} (h : lo ≤ hi) :
    (∑ i ∈ Finset.Ico lo hi,
      ((E.switchRoot N y b (i + 1) : X) - E.switchRoot N y b i)) =
        (E.switchRoot N y b hi : X) - E.switchRoot N y b lo := by
  exact Finset.sum_Ico_sub (fun i => (E.switchRoot N y b i : X)) h

end TreeEvaluation
end ReflexiveFixedPoints

end

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

theorem descendantLo_lt_hi (h : i ≤ j) (v : T.Node i) :
    T.descendantLo h v < T.descendantHi h v := by
  have hle := T.descendantFirst_le_of_ancestor_eq h v
    (T.descendantLast h v) (T.ancestorLE_descendantLast h v)
  exact Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp hle)

end ReflexiveFixedPoints.OrderedTree

end OAI

-- ---- from OAI.Analysis.Nonexpansive.SwitchingBlocks ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Actual whole-block switches and their vector telescope

The ordered descendant interval determines the actual before/after root states.
All leaf increments come from the same cutoff experiment.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

namespace OrderedTree

end OrderedTree

namespace TreeEvaluation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Multiplying the actual normalized increment by its positive path weight
recovers exactly the actual before-minus-after single-leaf difference. -/
theorem pathWeight_smul_switchVector (N : ℕ) (y : T.Node N → K) (b : K)
    (s : T.Node N) :
    W.pathWeight N s • E.switchVector N y b s =
      (E.switchRoot N y b (s.val + 1) : X) - E.switchRoot N y b s.val := by
  rw [switchVector, smul_smul, mul_inv_cancel₀ (ne_of_gt (W.pathWeight_pos N s)),
    one_smul]

/-- The sum of the actual normalized leaf increments over a descendant block
is exactly its actual before-minus-after root difference. -/
theorem switchVector_block_telescope {k N : ℕ} (h : k ≤ N)
    (y : T.Node N → K) (b : K) (v : T.Node k) :
    (∑ s ∈ T.descendants h v, W.pathWeight N s • E.switchVector N y b s) =
      (E.beforeBlock h y b v : X) - E.afterBlock h y b v := by
  calc
    (∑ s ∈ T.descendants h v, W.pathWeight N s • E.switchVector N y b s) =
        ∑ s ∈ T.descendants h v,
          ((E.switchRoot N y b (s.val + 1) : X) - E.switchRoot N y b s.val) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact E.pathWeight_smul_switchVector N y b s
    _ = ∑ i ∈ Finset.Ico (T.descendantLo h v) (T.descendantHi h v),
          ((E.switchRoot N y b (i + 1) : X) - E.switchRoot N y b i) :=
      T.sum_descendants_eq_Ico h v
        (fun i => (E.switchRoot N y b (i + 1) : X) - E.switchRoot N y b i)
    _ = (E.beforeBlock h y b v : X) - E.afterBlock h y b v :=
      E.switchRoot_interval_telescope N y b (le_of_lt (T.descendantLo_lt_hi h v))

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.switchVector_block_telescope := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.switchVector_block_telescope
