-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_scaled_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:50:40.619844+00:00
-- url     : https://prove2.me/submissions/e4c3c05b-d68e-43b8-b24d-cabd0c61fa80

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/TransmittedSubtreeErrors.lean:L55-L86
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_scaled_norm_sub_le. The node keeps its source
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
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_childAverage_norm_sub_le
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_sum_descendant_weighted_children

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

/-- The actual path weight times subtree sensitivity is bounded by the
weighted cutoff errors on that subtree's own descendants. -/
theorem subtreeOutput_scaled_norm_sub_le {k N : ℕ} (h : k ≤ N) :
    ∀ (H H' : T.Node N → K) (v : T.Node k),
      W.pathWeight k v *
          ‖(E.subtreeOutput h H v : X) - E.subtreeOutput h H' v‖ ≤
        ∑ s ∈ T.descendants h v, W.pathWeight N s * ‖(H s : X) - H' s‖ := by
  classical
  induction h using Nat.leRec with
  | refl =>
      intro H H' v
      have hdesc : T.descendants (Nat.le_refl k) v = {v} := by
        ext s
        simp only [T.mem_descendants, T.ancestorLE_refl_apply, Finset.mem_singleton]
      simpa only [E.subtreeOutput_refl_apply, hdesc, Finset.sum_singleton] using
        (le_refl (W.pathWeight k v * ‖(H v : X) - H' v‖))
  | @le_succ_of_le N h ih =>
      intro H H' v
      rw [E.subtreeOutput_step h, E.subtreeOutput_step h]
      calc
        _ ≤ ∑ p ∈ T.descendants h v, W.pathWeight N p *
            ‖(E.collapse N H p : X) - E.collapse N H' p‖ :=
          ih (E.collapse N H) (E.collapse N H') v
        _ ≤ ∑ p ∈ T.descendants h v, W.pathWeight N p *
            (∑ c ∈ Finset.univ.filter (fun c => T.parent N c = p),
              W.weight N c * ‖(H c : X) - H' c‖) := by
          apply Finset.sum_le_sum
          intro p hp
          exact mul_le_mul_of_nonneg_left (E.collapse_norm_sub_le N H H' p)
            (W.pathWeight_nonneg N p)
        _ = _ := sum_descendant_weighted_children (W := W) h v
          (fun c => ‖(H c : X) - H' c‖)

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_scaled_norm_sub_le.{u} := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_scaled_norm_sub_le.{u}
