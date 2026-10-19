-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.before_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:31:02.181703+00:00
-- url     : https://prove2.me/submissions/9c1b8d79-62ad-49eb-8357-47e3433e16a9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/BlockBefore.lean:L149-L167
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.before_block_bound. The node keeps its source
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
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_evaluate_focus_norm_sub_le

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

theorem weight_le_one (k : ℕ) (c : T.Node (k + 1)) : W.weight k c ≤ 1 := by
  calc
    W.weight k c ≤
        ∑ d ∈ Finset.univ.filter (fun d => T.parent k d = T.parent k c),
          W.weight k d :=
      Finset.single_le_sum (fun d _ => W.weight_nonneg k d) (by simp)
    _ = 1 := W.weight_sum k (T.parent k c)

theorem pathWeight_pos (k : ℕ) (v : T.Node k) : 0 < W.pathWeight k v := by
  induction k with
  | zero => exact zero_lt_one
  | succ k ih => exact mul_pos (ih (T.parent k v)) (W.weight_pos k v)

theorem pathWeight_nonneg (k : ℕ) (v : T.Node k) : 0 ≤ W.pathWeight k v :=
  (W.pathWeight_pos k v).le

theorem pathWeight_le_one (k : ℕ) (v : T.Node k) : W.pathWeight k v ≤ 1 := by
  induction k with
  | zero => exact le_refl 1
  | succ k ih =>
      calc
        W.pathWeight (k + 1) v =
            W.pathWeight k (T.parent k v) * W.weight k v := rfl
        _ ≤ 1 * 1 :=
          mul_le_mul (ih (T.parent k v)) (W.weight_le_one k v)
            (W.weight_nonneg k v) zero_le_one
        _ = 1 := one_mul 1

end WeightedTree
end ReflexiveFixedPoints

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

/-- Dropping path weights can only increase this sum of nonnegative errors. -/
theorem weightedPathDisplacement_le_pathDisplacement (k : ℕ) (v : T.Node k) (z : K) :
    E.weightedPathDisplacement k v z ≤ E.pathDisplacement k v z := by
  induction k with
  | zero => exact le_refl 0
  | succ k ih =>
      apply add_le_add (ih (T.parent k v))
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (W.pathWeight_le_one k (T.parent k v))
          (norm_nonneg ((E.map k (T.parent k v) z : X) - z))

/-- The before-block root bound from the actual focused cutoff error and the
actual unweighted ancestor displacement budget. -/
theorem before_block_bound
    (hdiam : ∀ a b : K, ‖(a : X) - b‖ ≤ 1)
    (k : ℕ) (H : T.Node k → K) (v : T.Node k) (z : K) {e : ℝ}
    (hfocused : ‖(H v : X) - z‖ ≤ e)
    (hpath : E.pathDisplacement k v z ≤ e) :
    ‖(E.evaluate k H : X) - z‖ ≤ 1 - W.pathWeight k v + 2 * e := by
  have he : 0 ≤ e := (norm_nonneg _).trans hfocused
  have hterm : W.pathWeight k v * ‖(H v : X) - z‖ ≤ e := by
    calc
      W.pathWeight k v * ‖(H v : X) - z‖ ≤ W.pathWeight k v * e :=
        mul_le_mul_of_nonneg_left hfocused (W.pathWeight_nonneg k v)
      _ ≤ 1 * e := mul_le_mul_of_nonneg_right (W.pathWeight_le_one k v) he
      _ = e := one_mul e
  have herr : E.weightedPathDisplacement k v z ≤ e :=
    (E.weightedPathDisplacement_le_pathDisplacement k v z).trans hpath
  have hfocus := E.evaluate_focus_norm_sub_le hdiam k H v z
  linarith

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.before_block_bound.{u} := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.before_block_bound.{u}
