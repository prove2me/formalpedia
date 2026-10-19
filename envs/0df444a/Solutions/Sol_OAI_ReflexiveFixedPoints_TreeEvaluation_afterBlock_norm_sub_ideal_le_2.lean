-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.afterBlock_norm_sub_ideal_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:56:36.948295+00:00
-- url     : https://prove2.me/submissions/bca2ad8c-eddc-4a7e-a29a-ce7342512964

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/BlockEstimates.lean:L54-L79
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.afterBlock_norm_sub_ideal_le. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Nonexpansive_BlockEstimates
import Theorems.Thm_OAI_ReflexiveFixedPoints_OrderedTree_lt_descendantLo_iff_ancestorLE_lt
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_descendantLevelDefect_le
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_evaluate_norm_sub_le
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_subtreeOutput_congr
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_subtreeOutput_const_scaled_norm_sub_le
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_subtreeOutput_labels_norm_sub_le
import Theorems.Thm_OAI_ReflexiveFixedPoints_WeightedTree_sum_pathWeight_parent

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

theorem sum_pathWeight (k : ℕ) : (∑ v, W.pathWeight k v) = 1 := by
  induction k with
  | zero => simp [pathWeight, OrderedTree.Node, T.size_zero]
  | succ k ih =>
      calc
        (∑ v, W.pathWeight (k + 1) v) = ∑ p, W.pathWeight k p := by
          simpa only [mul_one] using W.sum_pathWeight_parent k (fun _ => 1)
        _ = 1 := ih

end WeightedTree
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.TreeEvaluation ----
namespace OAI

/-!
# Actual nonlinear evaluation on a weighted ordered tree

The maps act on the literal subtype of a convex subset of a real normed
space. A cutoff value is an output: its own node map is not applied again.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TreeEvaluation

variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Uniform cutoff errors propagate with no increase to the root. -/
theorem evaluate_norm_sub_le_of_forall (k : ℕ) (H H' : T.Node k → K)
    {ε : ℝ} (hε : ∀ v, ‖(H v : X) - H' v‖ ≤ ε) :
    ‖(E.evaluate k H : X) - E.evaluate k H'‖ ≤ ε := by
  calc
    ‖(E.evaluate k H : X) - E.evaluate k H'‖ ≤
        ∑ v, W.pathWeight k v * ‖(H v : X) - H' v‖ :=
      E.evaluate_norm_sub_le k H H'
    _ ≤ ∑ v, W.pathWeight k v * ε := by
      exact Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_left (hε v) (le_of_lt (W.pathWeight_pos k v))
    _ = ε := by rw [← Finset.sum_mul, W.sum_pathWeight, one_mul]

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.SubtreeEvaluation ----
namespace OAI

/-!
# Actual evaluation of a subtree

Evaluation between two arbitrary levels is an iteration of the same
`collapse` operation used by root evaluation. The cutoff's own maps are
not applied. Composition gives both the root factorization and the
recurrence at the top of a subtree.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TreeEvaluation

variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

theorem subtreeOutput_congr_of_descendants {i j : ℕ} (h : i ≤ j)
    (H H' : T.Node j → K) (v : T.Node i)
    (heq : ∀ s ∈ T.descendants h v, H s = H' s) :
    E.subtreeOutput h H v = E.subtreeOutput h H' v := by
  apply E.subtreeOutput_congr h H H' v
  intro s hs
  exact heq s ((T.mem_descendants h v s).2 hs)

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.SubtreeErrors ----
namespace OAI

/-!
Errors of the actual nonlinear subtree evaluation.

An untouched subtree is compared to its map applied to the anchor. The proof
uses the actual collapse rule and child-average estimates at each internal
level. The local version follows from equality on descendant leaves.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints
namespace TreeEvaluation

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Only descendant leaves need be untouched; all other leaf states are arbitrary. -/
theorem subtreeOutput_untouched_norm_sub_le (x : K) (τ : ℕ → ℝ) {N : ℕ}
    (haverage : ∀ k, k < N → ∀ p : T.Node k,
      ‖(E.childAverage k (fun c => E.map (k + 1) c x) p : X) - x‖ ≤ τ k)
    {k : ℕ} (h : k ≤ N) (H : T.Node N → K) (v : T.Node k)
    (huntouched : ∀ s, T.ancestorLE h s = v → H s = E.map N s x) :
    ‖(E.subtreeOutput h H v : X) - E.map k v x‖ ≤
      ∑ d ∈ Finset.Ico k N, τ d := by
  rw [E.subtreeOutput_congr h H (fun s => E.map N s x) v huntouched]
  exact E.subtreeOutput_labels_norm_sub_le x τ haverage h v

end TreeEvaluation
end ReflexiveFixedPoints

end

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

/-- At the after-block cutoff, a leaf is unchanged exactly when its depth-k
ancestor is strictly to the left of the block's node. -/
theorem switchLeaves_afterBlock {k N : ℕ} (h : k ≤ N)
    (y : T.Node N → K) (b : K) (v : T.Node k) (s : T.Node N) :
    E.switchLeaves N y b (T.descendantLo h v) s =
      if T.ancestorLE h s < v then y s else b := by
  simp only [switchLeaves, T.lt_descendantLo_iff_ancestorLE_lt h v s]

end TreeEvaluation
end ReflexiveFixedPoints

end

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

/-- Summing the ancestor-weight comparisons gives the full unweighted
terminal displacement budget, multiplied by just the ancestor's weight. -/
theorem internalDescendantDefect_le {k : ℕ} (N : ℕ) (b : K) (v : T.Node k) :
    E.internalDescendantDefect N b v ≤ W.pathWeight k v * E.terminalDefect N b := by
  classical
  unfold internalDescendantDefect terminalDefect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  exact E.descendantLevelDefect_le v b d

/-- Constant terminal error is at most the total unweighted displacement.
Only positivity of this one path weight is used to cancel it. -/
theorem subtreeOutput_const_norm_sub_le_terminalDefect {k N : ℕ} (h : k ≤ N)
    (b : K) (v : T.Node k) :
    ‖(E.subtreeOutput h (fun _ => b) v : X) - b‖ ≤ E.terminalDefect N b := by
  exact (mul_le_mul_iff_right₀ (W.pathWeight_pos k v)).mp
    ((E.subtreeOutput_const_scaled_norm_sub_le h b v).trans
      (E.internalDescendantDefect_le N b v))

/-- A completely switched subtree has error bounded by the common terminal
budget, regardless of all terminal values outside that subtree. -/
theorem subtreeOutput_norm_sub_le_terminalDefect {k N : ℕ} (h : k ≤ N)
    (H : T.Node N → K) (b : K) (v : T.Node k)
    (heq : ∀ s ∈ T.descendants h v, H s = b) :
    ‖(E.subtreeOutput h H v : X) - b‖ ≤ E.terminalDefect N b := by
  rw [E.subtreeOutput_congr_of_descendants h H (fun _ => b) v heq]
  exact E.subtreeOutput_const_norm_sub_le_terminalDefect h b v

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.BlockEstimates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Detection of actual switched descendant blocks

The before and after estimates are proved for the actual root states.  The
ideal cutoff contains labels strictly to the left and the common terminal
point elsewhere.  Its identification with an earlier prediction is supplied
by the candidate construction, after which the terminal detector applies.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints
namespace TreeEvaluation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Uniform errors of untouched and transmitted subtrees give the actual
post-block root's distance from its ideal cutoff evaluation. -/
theorem afterBlock_norm_sub_ideal_le
    (x b : K) (τ : ℕ → ℝ) {k N : ℕ} (h : k ≤ N) (v : T.Node k)
    (haverage : ∀ d, d < N → ∀ p : T.Node d,
      ‖(E.childAverage d (fun c => E.map (d + 1) c x) p : X) - x‖ ≤ τ d)
    {e : ℝ} (htail : (∑ d ∈ Finset.Ico k N, τ d) ≤ e)
    (hterminal : E.terminalDefect N b ≤ e) :
    ‖(E.afterBlock h (fun s => E.map N s x) b v : X) -
      E.evaluate k (E.idealCutoff k x b v)‖ ≤ e := by
  unfold afterBlock switchRoot
  rw [E.evaluate_subtreeOutput h]
  apply E.evaluate_norm_sub_le_of_forall
  intro u
  by_cases huv : u < v
  · simp only [idealCutoff, ite_eq_left huv]
    refine (E.subtreeOutput_untouched_norm_sub_le x τ haverage h
      (E.switchLeaves N (fun s => E.map N s x) b (T.descendantLo h v)) u ?_).trans htail
    intro s hs
    rw [E.switchLeaves_afterBlock h (fun s => E.map N s x) b v s, hs, ite_eq_left huv]
  · simp only [idealCutoff, ite_eq_right huv]
    refine (E.subtreeOutput_norm_sub_le_terminalDefect h
      (E.switchLeaves N (fun s => E.map N s x) b (T.descendantLo h v)) b u ?_).trans hterminal
    intro s hs
    have hsu := (T.mem_descendants h u s).mp hs
    rw [E.switchLeaves_afterBlock h (fun s => E.map N s x) b v s, hsu, ite_eq_right huv]

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.afterBlock_norm_sub_ideal_le := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.afterBlock_norm_sub_ideal_le
