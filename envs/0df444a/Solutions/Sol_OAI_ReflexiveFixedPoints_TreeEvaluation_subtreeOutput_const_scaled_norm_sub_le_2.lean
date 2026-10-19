-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_const_scaled_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:54:27.862673+00:00
-- url     : https://prove2.me/submissions/97e1afe9-fdc5-4097-b370-fdd626d3e1af

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/TransmittedSubtreeErrors.lean:L152-L185
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_const_scaled_norm_sub_le. The node keeps its source
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
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_subtreeOutput_scaled_norm_sub_le

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

-- ---- from OAI.Analysis.Nonexpansive.TransmittedSubtreeErrors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
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

theorem internalDescendantDefect_succ {k N : ℕ} (h : k ≤ N) (b : K)
    (v : T.Node k) :
    E.internalDescendantDefect (N + 1) b v = E.internalDescendantDefect N b v +
      ∑ s ∈ T.descendants h v, W.pathWeight N s * ‖(E.map N s b : X) - b‖ := by
  classical
  simp only [internalDescendantDefect, Finset.sum_range_succ,
    descendantLevelDefect, dite_eq_left h]

/-- Exact scaled transmitted bound for a constant terminal assignment. -/
theorem subtreeOutput_const_scaled_norm_sub_le {k N : ℕ} (h : k ≤ N)
    (b : K) (v : T.Node k) :
    W.pathWeight k v * ‖(E.subtreeOutput h (fun _ => b) v : X) - b‖ ≤
      E.internalDescendantDefect N b v := by
  classical
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le N h ih =>
      rw [E.subtreeOutput_step h, E.internalDescendantDefect_succ h]
      have hs : W.pathWeight k v *
          ‖(E.subtreeOutput h (E.collapse N (fun _ => b)) v : X) -
            E.subtreeOutput h (fun _ => b) v‖ ≤
          ∑ s ∈ T.descendants h v,
            W.pathWeight N s * ‖(E.map N s b : X) - b‖ := by
        simpa only [collapse, E.childAverage_const] using
          E.subtreeOutput_scaled_norm_sub_le h
            (E.collapse N (fun _ => b)) (fun _ => b) v
      calc
        _ ≤ W.pathWeight k v *
            (‖(E.subtreeOutput h (E.collapse N (fun _ => b)) v : X) -
                E.subtreeOutput h (fun _ => b) v‖ +
              ‖(E.subtreeOutput h (fun _ => b) v : X) - b‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub _ _ _)
            (W.pathWeight_nonneg k v)
        _ = W.pathWeight k v *
            ‖(E.subtreeOutput h (E.collapse N (fun _ => b)) v : X) -
              E.subtreeOutput h (fun _ => b) v‖ +
            W.pathWeight k v * ‖(E.subtreeOutput h (fun _ => b) v : X) - b‖ :=
          mul_add _ _ _
        _ ≤ (∑ s ∈ T.descendants h v,
            W.pathWeight N s * ‖(E.map N s b : X) - b‖) +
              E.internalDescendantDefect N b v := add_le_add hs ih
        _ = _ := add_comm _ _

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_const_scaled_norm_sub_le.{u} := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_const_scaled_norm_sub_le.{u}
