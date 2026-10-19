-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.OrderedTree.exists_feasible_branch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T18:05:10.880101+00:00
-- url     : https://prove2.me/submissions/dbc34495-6a3b-4614-be88-3049a043c893

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/FeasibleBranch.lean:L71-L98
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.OrderedTree.exists_feasible_branch. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Nonexpansive_LedgerPredictionLimits
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidatePredictions
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateAncestors
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateDetectors
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeTolerance
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateTolerance
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateTreeTolerance
import Definitions.Def_OAI_Analysis_Nonexpansive_SwitchingTreeData
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeProducer
import Definitions.Def_OAI_Analysis_Nonexpansive_WeightedDeficit
import Definitions.Def_OAI_Analysis_Nonexpansive_FiniteWitness
import Definitions.Def_OAI_Analysis_Nonexpansive_FeasibleBranch

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

theorem ancestorLE_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    T.ancestorLE (Nat.le_trans hij hjk) =
      T.ancestorLE hij ∘ T.ancestorLE hjk := by
  induction hjk using Nat.leRec with
  | refl => simp
  | @le_succ_of_le k h ih =>
      rw [T.ancestorLE_step (Nat.le_trans hij h), T.ancestorLE_step h, ih]
      rfl

theorem ancestorLE_trans_apply {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (v : T.Node k) :
    T.ancestorLE (Nat.le_trans hij hjk) v =
      T.ancestorLE hij (T.ancestorLE hjk v) := by
  rw [T.ancestorLE_trans hij hjk]
  rfl

end OrderedTree
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.FeasibleBranch ----
namespace OAI

/-!
# A feasible branch with finite prefix witnesses

Feasibility is an existential proposition on a finite node, so the feasible
nodes at each level still form a finite type. Restriction to an ancestor
preserves the same witness. The elementary graded form of König's lemma
then yields one coherent branch, with a witness for every finite prefix.

The witness set is arbitrary. In the fixed-point argument it is instantiated
with the whole unit ball of the closed difference span. No compactness or
surjectivity of projections between feasible levels is used here.
-/

namespace ReflexiveFixedPoints
namespace OrderedTree

variable (T : OrderedTree) {D : Type*}

variable (B : Set D) (f : (k : ℕ) → T.Node k → D → ℝ)

/-- Ancestor restriction keeps the original witness and every earlier constraint. -/
theorem detectsPrefix_ancestorLE {i j : ℕ} (hij : i ≤ j)
    {v : T.Node j} {d : D} (hd : T.DetectsPrefix f v d) :
    T.DetectsPrefix f (T.ancestorLE hij v) d := by
  intro k hk hpos
  rw [← T.ancestorLE_trans_apply hk hij]
  exact hd k (hk.trans hij) hpos

theorem feasible_ancestorLE {i j : ℕ} (hij : i ≤ j)
    {v : T.Node j} (hv : T.Feasible B f v) :
    T.Feasible B f (T.ancestorLE hij v) := by
  obtain ⟨d, hdB, hd⟩ := hv
  exact ⟨d, hdB, T.detectsPrefix_ancestorLE f hij hd⟩

/-- A feasible node at every depth yields a coherent feasible branch. -/
theorem exists_feasible_branch
    (hne : ∀ n, ∃ v : T.Node n, T.Feasible B f v) :
    ∃ b : (n : ℕ) → T.Node n,
      T.IsBranch b ∧ ∀ n, T.Feasible B f (b n) := by
  classical
  let : ∀ n, Nonempty (T.FeasibleNode B f n) := fun n => by
    obtain ⟨v, hv⟩ := hne n
    exact ⟨⟨v, hv⟩⟩
  let π : {i j : ℕ} → i ≤ j → T.FeasibleNode B f j → T.FeasibleNode B f i :=
    fun {_ _} hij v => ⟨T.ancestorLE hij v.val,
      T.feasible_ancestorLE B f hij v.property⟩
  have hπrefl : ∀ ⦃i⦄ (v : T.FeasibleNode B f i), π (le_refl i) v = v := by
    intro i v
    apply Subtype.ext
    exact T.ancestorLE_refl_apply i v.val
  have hπtrans : ∀ ⦃i j k⦄ (hij : i ≤ j) (hjk : j ≤ k)
      (v : T.FeasibleNode B f k),
      π hij (π hjk v) = π (hij.trans hjk) v := by
    intro i j k hij hjk v
    apply Subtype.ext
    exact (T.ancestorLE_trans_apply hij hjk v.val).symm
  obtain ⟨b, hb⟩ := exists_seq_forall_proj_of_forall_finite
    (α := fun n => T.FeasibleNode B f n) π hπrefl hπtrans
    (fun _ _ => Set.toFinite _)
  refine ⟨fun n => (b n).val, ?_, fun n => (b n).property⟩
  intro i j hij
  exact congrArg (fun v : T.FeasibleNode B f i => v.val) (hb hij)

end OrderedTree
end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.OrderedTree


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.OrderedTree.exists_feasible_branch := @_root_.OAI.ReflexiveFixedPoints.OrderedTree.exists_feasible_branch
