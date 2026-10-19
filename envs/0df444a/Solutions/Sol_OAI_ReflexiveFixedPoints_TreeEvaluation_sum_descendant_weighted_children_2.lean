-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.sum_descendant_weighted_children
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:48:37.130511+00:00
-- url     : https://prove2.me/submissions/dce2841f-e517-44e2-a799-86d04295581f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/TransmittedSubtreeErrors.lean:L34-L53
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.sum_descendant_weighted_children. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Nonexpansive_TransmittedSubtreeErrors

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

theorem ancestorLE_step_apply {i j : ℕ} (h : i ≤ j) (v : T.Node (j + 1)) :
    T.ancestorLE (Nat.le_succ_of_le h) v = T.ancestorLE h (T.parent j v) := by
  rw [T.ancestorLE_step h]
  rfl

end OrderedTree
end ReflexiveFixedPoints

end OAI

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

/-- Partition a finite sum by the fibers of a function. -/
theorem sum_fiber_partition {A B M : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] [AddCommMonoid M] (f : A → B) (g : A → M) :
    (∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), g a) = ∑ a, g a := by
  classical
  exact Finset.sum_fiberwise Finset.univ f g

/-- Regroup a weighted finite sum by the fibers of a function. -/
theorem sum_fiber_mul {A B R : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] [NonUnitalNonAssocSemiring R]
    (f : A → B) (r : B → R) (g : A → R) :
    (∑ b, r b * (∑ a ∈ Finset.univ.filter (fun a => f a = b), g a)) =
      ∑ a, r (f a) * g a := by
  classical
  calc
    _ = ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), r (f a) * g a := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := sum_fiber_partition f _

namespace WeightedTree

variable {T : OrderedTree} (W : WeightedTree T)

end WeightedTree
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.TransmittedSubtreeErrors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Error transmitted from constant terminal values

Every map displacement is counted at its actual node, with its actual path
weight.  The proof follows the concrete finite evaluator.  No positive
uniform lower bound on the weights and no affine property of the node maps
is needed.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TreeEvaluation

variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Regroup the weighted children of the descendants at one level. -/
theorem sum_descendant_weighted_children {k n : ℕ} (h : k ≤ n)
    (v : T.Node k) (f : T.Node (n + 1) → ℝ) :
    (∑ p ∈ T.descendants h v, W.pathWeight n p *
      (∑ c ∈ Finset.univ.filter (fun c => T.parent n c = p), W.weight n c * f c)) =
      ∑ c ∈ T.descendants (Nat.le_succ_of_le h) v, W.pathWeight (n + 1) c * f c := by
  classical
  calc
    _ = ∑ p, (if T.ancestorLE h p = v then W.pathWeight n p else 0) *
        (∑ c ∈ Finset.univ.filter (fun c => T.parent n c = p), W.weight n c * f c) := by
      simp only [OrderedTree.descendants, Finset.sum_filter, ite_mul, zero_mul]
    _ = ∑ c, (if T.ancestorLE h (T.parent n c) = v then
        W.pathWeight n (T.parent n c) else 0) * (W.weight n c * f c) :=
      sum_fiber_mul (T.parent n)
        (fun p => if T.ancestorLE h p = v then W.pathWeight n p else 0)
        (fun c => W.weight n c * f c)
    _ = _ := by
      simp only [OrderedTree.descendants, Finset.sum_filter,
        T.ancestorLE_step_apply h, WeightedTree.pathWeight_succ,
        ite_mul, zero_mul, mul_assoc]

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.sum_descendant_weighted_children := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.sum_descendant_weighted_children
