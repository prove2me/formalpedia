-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_congr
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:15:32.770408+00:00
-- url     : https://prove2.me/submissions/59dcb37b-1338-48dc-841c-df58aad7465a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/SubtreeEvaluation.lean:L115-L133
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_congr. The node keeps its source
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

/-- A child average depends only on the children belonging to that parent. -/
theorem childAverage_congr (k : ℕ) (H H' : T.Node (k + 1) → K)
    (p : T.Node k) (heq : ∀ c, T.parent k c = p → H c = H' c) :
    E.childAverage k H p = E.childAverage k H' p := by
  apply Subtype.ext
  simp only [E.childAverage_val]
  apply Finset.sum_congr rfl
  intro c hc
  rw [heq c (Finset.mem_filter.mp hc).2]

/-- The nonlinear parent map preserves equality of its actual child input. -/
theorem collapse_congr (k : ℕ) (H H' : T.Node (k + 1) → K)
    (p : T.Node k) (heq : ∀ c, T.parent k c = p → H c = H' c) :
    E.collapse k H p = E.collapse k H' p := by
  unfold collapse
  rw [E.childAverage_congr k H H' p heq]

/-- A subtree output depends only on the cutoff values below that node. -/
theorem subtreeOutput_congr {i j : ℕ} (h : i ≤ j) :
    ∀ (H H' : T.Node j → K) (v : T.Node i),
      (∀ s, T.ancestorLE h s = v → H s = H' s) →
      E.subtreeOutput h H v = E.subtreeOutput h H' v := by
  induction h using Nat.leRec with
  | refl =>
      intro H H' v heq
      simpa only [E.subtreeOutput_refl_apply] using heq v (by simp)
  | @le_succ_of_le j h ih =>
      intro H H' v heq
      rw [E.subtreeOutput_step h, E.subtreeOutput_step h]
      apply ih (E.collapse j H) (E.collapse j H') v
      intro p hp
      apply E.collapse_congr j H H' p
      intro c hc
      apply heq c
      rw [T.ancestorLE_step_apply h, hc]
      exact hp

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_congr.{u} := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.subtreeOutput_congr.{u}
