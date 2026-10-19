-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.descendantLevelDefect_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:52:24.511973+00:00
-- url     : https://prove2.me/submissions/34bd9711-11e8-49f5-9848-c5fae52c67c2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/TransmittedSubtreeErrors.lean:L121-L139
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.descendantLevelDefect_le. The node keeps its source
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
import Theorems.Thm_OAI_ReflexiveFixedPoints_WeightedTree_sum_pathWeight_parent

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

namespace WeightedTree

variable {T : OrderedTree} (W : WeightedTree T)

theorem pathWeight_pos (k : ℕ) (v : T.Node k) : 0 < W.pathWeight k v := by
  induction k with
  | zero => exact zero_lt_one
  | succ k ih => exact mul_pos (ih (T.parent k v)) (W.weight_pos k v)

theorem pathWeight_nonneg (k : ℕ) (v : T.Node k) : 0 ≤ W.pathWeight k v :=
  (W.pathWeight_pos k v).le

/-- Every ancestor map pushes later-level path masses to earlier-level masses. -/
theorem sum_pathWeight_ancestor {i j : ℕ} (h : i ≤ j) (f : T.Node i → ℝ) :
    (∑ v, W.pathWeight j v * f (T.ancestorLE h v)) =
      ∑ p, W.pathWeight i p * f p := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le j h ih =>
      calc
        _ = ∑ v, W.pathWeight (j + 1) v * f (T.ancestorLE h (T.parent j v)) := by
          simp only [T.ancestorLE_step_apply h]
        _ = ∑ p, W.pathWeight j p * f (T.ancestorLE h p) :=
          W.sum_pathWeight_parent j (fun p => f (T.ancestorLE h p))
        _ = _ := ih

/-- The total mass below a node is exactly that node's path mass. -/
theorem descendant_sum_pathWeight {i j : ℕ} (h : i ≤ j) (p : T.Node i) :
    (∑ v ∈ T.descendants h p, W.pathWeight j v) = W.pathWeight i p := by
  classical
  have hf := W.sum_pathWeight_ancestor h (fun q => if q = p then (1 : ℝ) else 0)
  simpa [OrderedTree.descendants, Finset.sum_filter, mul_ite] using hf

theorem pathWeight_le_ancestor {i j : ℕ} (h : i ≤ j) (v : T.Node j) :
    W.pathWeight j v ≤ W.pathWeight i (T.ancestorLE h v) := by
  calc
    W.pathWeight j v ≤
        ∑ s ∈ T.descendants h (T.ancestorLE h v), W.pathWeight j s :=
      Finset.single_le_sum (fun s _ => W.pathWeight_nonneg j s) (by simp)
    _ = _ := W.descendant_sum_pathWeight h (T.ancestorLE h v)

end WeightedTree
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.TransmittedSubtreeErrors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
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

/-- Every descendant path weight is at most its ancestor's path weight. -/
theorem descendantLevelDefect_le {k : ℕ} (v : T.Node k) (b : K) (d : ℕ) :
    E.descendantLevelDefect v b d ≤
      W.pathWeight k v * ∑ s : T.Node d, ‖(E.map d s b : X) - b‖ := by
  classical
  unfold descendantLevelDefect
  split_ifs with hd
  · rw [OrderedTree.descendants, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    by_cases hancestor : T.ancestorLE hd s = v
    · rw [ite_eq_left hancestor]
      have hweight : W.pathWeight d s ≤ W.pathWeight k v := by
        simpa only [hancestor] using W.pathWeight_le_ancestor hd s
      exact mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
    · rw [ite_eq_right hancestor]
      exact mul_nonneg (W.pathWeight_nonneg k v) (norm_nonneg _)
  · exact mul_nonneg (W.pathWeight_nonneg k v)
      (Finset.sum_nonneg fun s _ => norm_nonneg _)

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.descendantLevelDefect_le.{u} := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.descendantLevelDefect_le.{u}
