-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.evaluate_focus_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:28:34.304197+00:00
-- url     : https://prove2.me/submissions/c7d8b804-60ee-46c3-adea-1089e58b4930

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/BlockBefore.lean:L117-L147
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.evaluate_focus_norm_sub_le. The node keeps its source
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
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_childAverage_norm_sub_le
import Theorems.Thm_OAI_ReflexiveFixedPoints_weighted_focus_sum_le

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

theorem eq_root (v : T.Node 0) : v = T.root := by
  apply Fin.ext
  have hv : v.val < 1 := T.size_zero ▸ v.isLt
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hv)

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

/-- Each actual parent map is nonexpansive after taking its child average. -/
theorem collapse_norm_sub_le (k : ℕ) (H H' : T.Node (k + 1) → K)
    (p : T.Node k) :
    ‖(E.collapse k H p : X) - E.collapse k H' p‖ ≤
      ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - H' c‖ := by
  have hm : ‖(E.collapse k H p : X) - E.collapse k H' p‖ ≤
      ‖(E.childAverage k H p : X) - E.childAverage k H' p‖ := by
    simpa only [collapse, Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      using (E.nonexpansive k p).dist_le_mul (E.childAverage k H p)
        (E.childAverage k H' p)
  exact hm.trans (E.childAverage_norm_sub_le k H H' p)

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

/-- One actual collapse transmits a constant up to the node's displacement. -/
theorem collapse_norm_sub_point_le (k : ℕ) (H : T.Node (k + 1) → K)
    (b : K) (p : T.Node k) :
    ‖(E.collapse k H p : X) - b‖ ≤
      (∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - b‖) + ‖(E.map k p b : X) - b‖ := by
  have hcompare : ‖(E.collapse k H p : X) - E.map k p b‖ ≤
      ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - b‖ := by
    simpa only [collapse, E.childAverage_const] using
      E.collapse_norm_sub_le k H (fun _ => b) p
  calc
    ‖(E.collapse k H p : X) - b‖ ≤
        ‖(E.collapse k H p : X) - E.map k p b‖ +
          ‖(E.map k p b : X) - b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add_left hcompare _

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.BlockBefore ----
namespace OAI

/-!
# The actual root output before switching a descendant block

We follow one node through the recursive nonlinear evaluation.  The other
child outputs contribute at most their total weight because they lie in a
set of diameter at most one.  The error along the chosen path is the actual
displacement of its ancestor maps at the comparison point.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

namespace TreeEvaluation

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Focus one actual child while bounding all off-path child outputs by the
diameter of the set.  The node map is used only through nonexpansiveness. -/
theorem collapse_focus_norm_sub_le
    (hdiam : ∀ a b : K, ‖(a : X) - b‖ ≤ 1)
    (k : ℕ) (H : T.Node (k + 1) → K) (v : T.Node (k + 1)) (z : K) :
    ‖(E.collapse k H (T.parent k v) : X) - z‖ ≤
      W.weight k v * ‖(H v : X) - z‖ + (1 - W.weight k v) +
        ‖(E.map k (T.parent k v) z : X) - z‖ := by
  classical
  have hsum := weighted_focus_sum_le
    (Finset.univ.filter (fun c => T.parent k c = T.parent k v))
    (W.weight k) (fun c => ‖(H c : X) - z‖) v (by simp)
    (fun c _ => W.weight_nonneg k c) (W.weight_sum k (T.parent k v))
    (fun c _ _ => hdiam (H c) z)
  exact (E.collapse_norm_sub_point_le k H z (T.parent k v)).trans
    (add_le_add_left hsum _)

/-- Follow one selected cutoff value through the actual nonlinear evaluation.
No affinity or positive lower bound on path weights is used. -/
theorem evaluate_focus_norm_sub_le
    (hdiam : ∀ a b : K, ‖(a : X) - b‖ ≤ 1)
    (k : ℕ) (H : T.Node k → K) (v : T.Node k) (z : K) :
    ‖(E.evaluate k H : X) - z‖ ≤
      W.pathWeight k v * ‖(H v : X) - z‖ + (1 - W.pathWeight k v) +
        E.weightedPathDisplacement k v z := by
  induction k with
  | zero => simp [evaluate, weightedPathDisplacement, T.eq_root v]
  | succ k ih =>
      have hstep := E.collapse_focus_norm_sub_le hdiam k H v z
      calc
        ‖(E.evaluate (k + 1) H : X) - z‖ ≤
            W.pathWeight k (T.parent k v) *
              ‖(E.collapse k H (T.parent k v) : X) - z‖ +
              (1 - W.pathWeight k (T.parent k v)) +
                E.weightedPathDisplacement k (T.parent k v) z :=
          ih (E.collapse k H) (T.parent k v)
        _ ≤ W.pathWeight k (T.parent k v) *
              (W.weight k v * ‖(H v : X) - z‖ + (1 - W.weight k v) +
                ‖(E.map k (T.parent k v) z : X) - z‖) +
              (1 - W.pathWeight k (T.parent k v)) +
                E.weightedPathDisplacement k (T.parent k v) z :=
          add_le_add_left (add_le_add_left
            (mul_le_mul_of_nonneg_left hstep (W.pathWeight_nonneg k _)) _) _
        _ = W.pathWeight (k + 1) v * ‖(H v : X) - z‖ +
              (1 - W.pathWeight (k + 1) v) +
                E.weightedPathDisplacement (k + 1) v z := by
          rw [W.pathWeight_succ, E.weightedPathDisplacement_succ]
          ring

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.evaluate_focus_norm_sub_le.{u} := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.evaluate_focus_norm_sub_le.{u}
