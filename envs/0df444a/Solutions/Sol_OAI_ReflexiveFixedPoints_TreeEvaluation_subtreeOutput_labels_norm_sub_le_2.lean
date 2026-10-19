-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_labels_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:18:57.837225+00:00
-- url     : https://prove2.me/submissions/f9062ab4-2bdd-43d6-b8d7-5e2a771c9cfd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/SubtreeErrors.lean:L74-L106
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_labels_norm_sub_le. The node keeps its source
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
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_childAverage_norm_sub_le

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

/-- Evaluating through two consecutive intervals equals their actual composite. -/
theorem subtreeOutput_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (H : T.Node k → K) :
    E.subtreeOutput hij (E.subtreeOutput hjk H) =
      E.subtreeOutput (hij.trans hjk) H := by
  induction hjk using Nat.leRec with
  | refl => simp only [E.subtreeOutput_refl_apply]
  | @le_succ_of_le k hjk ih =>
      rw [E.subtreeOutput_step hjk, E.subtreeOutput_step (hij.trans hjk)]
      exact ih (E.collapse k H)

/-- The recursive rule at the top of a subtree uses its actual child outputs. -/
theorem subtreeOutput_top_step {i j : ℕ} (h : i ≤ j) (hnext : i + 1 ≤ j)
    (H : T.Node j → K) :
    E.subtreeOutput h H = E.collapse i (E.subtreeOutput hnext H) := by
  calc
    E.subtreeOutput h H =
        E.subtreeOutput (Nat.le_succ i) (E.subtreeOutput hnext H) :=
      (E.subtreeOutput_comp (Nat.le_succ i) hnext H).symm
    _ = _ := E.subtreeOutput_succ i _

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

/-- Each assigned map is nonexpansive in the original ambient norm. -/
theorem map_norm_sub_le (k : ℕ) (p : T.Node k) (a b : K) :
    ‖(E.map k p a : X) - E.map k p b‖ ≤ ‖(a : X) - b‖ := by
  simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    using (E.nonexpansive k p).dist_le_mul a b

/-- Compare an actual parent output to the parent's prescribed anchor label. -/
theorem collapse_norm_sub_label_le (k : ℕ) (H : T.Node (k + 1) → K)
    (x : K) (p : T.Node k) :
    ‖(E.collapse k H p : X) - E.map k p x‖ ≤
      (∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - E.map (k + 1) c x‖) +
      ‖(E.childAverage k (fun c => E.map (k + 1) c x) p : X) - x‖ := by
  calc
    ‖(E.collapse k H p : X) - E.map k p x‖ ≤
        ‖(E.collapse k H p : X) -
          E.collapse k (fun c => E.map (k + 1) c x) p‖ +
        ‖(E.collapse k (fun c => E.map (k + 1) c x) p : X) -
          E.map k p x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add
      (E.collapse_norm_sub_le k H (fun c => E.map (k + 1) c x) p)
      (E.map_norm_sub_le k p
        (E.childAverage k (fun c => E.map (k + 1) c x) p) x)

/-- The canonical untouched subtree incurs the sum of its finite level errors. -/
theorem subtreeOutput_labels_norm_sub_le (x : K) (τ : ℕ → ℝ) {N : ℕ}
    (haverage : ∀ k, k < N → ∀ p : T.Node k,
      ‖(E.childAverage k (fun c => E.map (k + 1) c x) p : X) - x‖ ≤ τ k)
    {k : ℕ} (h : k ≤ N) (v : T.Node k) :
    ‖(E.subtreeOutput h (fun s => E.map N s x) v : X) - E.map k v x‖ ≤
      ∑ d ∈ Finset.Ico k N, τ d := by
  classical
  induction h using Nat.decreasingInduction with
  | self => simp
  | of_succ k hk ih =>
      rw [E.subtreeOutput_top_step (Nat.le_of_lt hk) hk]
      calc
        ‖(E.collapse k (E.subtreeOutput hk (fun s => E.map N s x)) v : X) -
            E.map k v x‖ ≤
            (∑ c ∈ Finset.univ.filter (fun c => T.parent k c = v),
              W.weight k c *
                ‖(E.subtreeOutput hk (fun s => E.map N s x) c : X) -
                  E.map (k + 1) c x‖) + τ k :=
          (E.collapse_norm_sub_label_le k
            (E.subtreeOutput hk (fun s => E.map N s x)) x v).trans
            (add_le_add_right (haverage k hk v) _)
        _ ≤ (∑ c ∈ Finset.univ.filter (fun c => T.parent k c = v),
              W.weight k c * (∑ d ∈ Finset.Ico (k + 1) N, τ d)) + τ k := by
          apply add_le_add_left
          apply Finset.sum_le_sum
          intro c _
          exact mul_le_mul_of_nonneg_left (ih c) (W.weight_nonneg k c)
        _ = (∑ d ∈ Finset.Ico (k + 1) N, τ d) + τ k := by
          rw [← Finset.sum_mul, W.weight_sum, one_mul]
        _ = ∑ d ∈ Finset.Ico k N, τ d := by
          rw [Finset.sum_eq_sum_Ico_succ_bot hk τ]
          exact add_comm _ _

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_labels_norm_sub_le.{u} := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_labels_norm_sub_le.{u}
