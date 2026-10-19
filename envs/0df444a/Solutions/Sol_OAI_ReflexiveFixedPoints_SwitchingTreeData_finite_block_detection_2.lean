-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.SwitchingTreeData.finite_block_detection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T18:11:08.231987+00:00
-- url     : https://prove2.me/submissions/66b5ce5a-1d3a-4471-8732-deba09862e47

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/TreeFiniteWitness.lean:L96-L125
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.SwitchingTreeData.finite_block_detection. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeFiniteWitness
import Theorems.Thm_OAI_ReflexiveFixedPoints_OrderedTree_lt_descendantHi_iff_ancestorLE_le
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_afterBlock_norm_sub_ideal_le
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_before_block_bound
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_subtreeOutput_congr
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_subtreeOutput_labels_norm_sub_le
import Theorems.Thm_OAI_ReflexiveFixedPoints_dyadic_weighted_tail_le

-- ---- from OAI.Analysis.Nonexpansive.TreeBudget ----
namespace OAI

/-!
# Budgets attached to retained candidate ordinals

The label of a retained node is its zero-based ordinal in the global candidate
sequence.  Thus the one-based label `ℓ = label + 1` gives the budget
`2 ^ (-ℓ - 8) = (1 / 2) ^ (label + 9)`.  Injectivity, rather than a new
enumeration of retained nodes, compares their total with the candidate series.
The actual tree construction supplies this label and its injectivity proof.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

namespace OrderedTree

variable {T : OrderedTree}

theorem retainedBudget_pos (label : T.NonrootNode → ℕ) (v : T.NonrootNode) :
    0 < retainedBudget label v :=
  candidateBudget_pos (label v)

end OrderedTree
end ReflexiveFixedPoints

end

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

-- ---- from OAI.Analysis.Nonexpansive.SwitchingScalar ----
namespace OAI

/-!
# Scalar estimates for finite leaf switching

The first estimates telescope the actual scaled ancestor recurrence.  The
second estimates bound a finite dyadic tolerance tail, including an empty
tail.  These lemmas involve only real scalars and finite sums; the switching
construction supplies their hypotheses from its actual maps and weights.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

/-- The same finite tail is at most the budget at its initial level. -/
theorem dyadic_weighted_tail_le_initial (M : ℕ → ℝ)
    (hM_nonneg : ∀ d, 0 ≤ M d) (hM_anti : Antitone M)
    (k N : ℕ) (hkN : k ≤ N) :
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M d) ≤ M k := by
  calc
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M d) ≤
        (1 / 2 : ℝ) ^ k * M k :=
      dyadic_weighted_tail_le M hM_nonneg hM_anti k N hkN
    _ ≤ 1 * M k := mul_le_mul_of_nonneg_right
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) (hM_nonneg k)
    _ = M k := one_mul _

/-- Uniform comparison with any particular node budget at the same level. -/
theorem dyadic_weighted_tail_le_budget (M : ℕ → ℝ)
    (hM_nonneg : ∀ d, 0 ≤ M d) (hM_anti : Antitone M)
    (k N : ℕ) (hkN : k ≤ N) {e : ℝ} (hbudget : M k ≤ e) :
    (∑ d ∈ Finset.Ico k N, (1 / 2 : ℝ) ^ (d + 1) * M d) ≤ e :=
  (dyadic_weighted_tail_le_initial M hM_nonneg hM_anti k N hkN).trans hbudget

end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.SwitchingNorm ----
namespace OAI

/-!
# Norm estimates for the actual switching differences

These elementary estimates are applied to root outputs from one chronological
switching experiment.  The construction of those outputs and their before- and
after-block bounds is separate from the linear-functional calculations here.
-/

noncomputable section

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A functional of operator norm at most one is bounded by the given norm. -/
theorem abs_functional_apply_le_norm (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) (z : X) :
    |f z| ≤ ‖z‖ := by
  calc
    |f z| = ‖f z‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f‖ * ‖z‖ := f.le_opNorm z
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg z)
    _ = ‖z‖ := one_mul _

/-- Transfer a detector from two comparison points to the actual before/after
outputs.  This uses linearity only of the detector, not of the node maps. -/
theorem detector_transfer_le (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1)
    (U V y q : X) :
    f (y - q) - ‖U - y‖ - ‖V - q‖ ≤ f (U - V) := by
  have hU := abs_functional_apply_le_norm f hf (U - y)
  have hV := abs_functional_apply_le_norm f hf (V - q)
  have hU' := (abs_le.mp hU).1
  have hV' := (abs_le.mp hV).2
  have heq : f (U - V) = f (y - q) + f (U - y) - f (V - q) := by
    simp only [map_sub]
    ring
  linarith

/-- The exact `W - 5e` detector estimate from the three already proved actual
terminal, before-block, and after-block inequalities. -/
theorem block_detection_of_norm_bounds (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1)
    (U V y q : X) (W e : ℝ)
    (hterminal : 1 - 2 * e ≤ f (y - q))
    (hbefore : ‖U - y‖ ≤ 1 - W + 2 * e)
    (hafter : ‖V - q‖ ≤ e) :
    W - 5 * e ≤ f (U - V) := by
  have htransfer := detector_transfer_le f hf U V y q
  linarith

end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.SwitchingBlocks ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

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

/-- At the before-block cutoff, a leaf is unchanged exactly when its depth-k
ancestor is at or to the left of the block's node. -/
theorem switchLeaves_beforeBlock {k N : ℕ} (h : k ≤ N)
    (y : T.Node N → K) (b : K) (v : T.Node k) (s : T.Node N) :
    E.switchLeaves N y b (T.descendantHi h v) s =
      if T.ancestorLE h s ≤ v then y s else b := by
  simp only [switchLeaves, T.lt_descendantHi_iff_ancestorLE_le h v s]

/-- A node's own descendants are all unchanged immediately before its block. -/
theorem switchLeaves_beforeBlock_of_descendant {k N : ℕ} (h : k ≤ N)
    (y : T.Node N → K) (b : K) (v : T.Node k) (s : T.Node N)
    (hs : T.ancestorLE h s = v) :
    E.switchLeaves N y b (T.descendantHi h v) s = y s := by
  rw [E.switchLeaves_beforeBlock h y b v s, hs, ite_eq_left le_rfl]

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.BlockEstimates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

/-- The actual before-block root is close to the selected node's label. -/
theorem beforeBlock_norm_sub_label_le
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1)
    (x b : K) (τ : ℕ → ℝ) {k N : ℕ} (h : k ≤ N) (v : T.Node k)
    (haverage : ∀ d, d < N → ∀ p : T.Node d,
      ‖(E.childAverage d (fun c => E.map (d + 1) c x) p : X) - x‖ ≤ τ d)
    {e : ℝ} (htail : (∑ d ∈ Finset.Ico k N, τ d) ≤ e)
    (hpath : E.pathDisplacement k v (E.map k v x) ≤ e) :
    ‖(E.beforeBlock h (fun s => E.map N s x) b v : X) - E.map k v x‖ ≤
      1 - W.pathWeight k v + 2 * e := by
  unfold beforeBlock switchRoot
  rw [E.evaluate_subtreeOutput h]
  apply E.before_block_bound hdiam k _ v (E.map k v x)
  · refine (E.subtreeOutput_untouched_norm_sub_le x τ haverage h
      (E.switchLeaves N (fun s => E.map N s x) b (T.descendantHi h v)) v ?_).trans htail
    intro s hs
    exact E.switchLeaves_beforeBlock_of_descendant h (fun s => E.map N s x) b v s hs
  · exact hpath

/-- The exact `W_v - 5e_v` lower bound for an actual before-minus-after block
increment, proved from the actual child averages and ancestor displacements. -/
theorem actual_block_detection
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1)
    (x b : K) (τ : ℕ → ℝ) {k N : ℕ} (h : k ≤ N) (v : T.Node k)
    (haverage : ∀ d, d < N → ∀ p : T.Node d,
      ‖(E.childAverage d (fun c => E.map (d + 1) c x) p : X) - x‖ ≤ τ d)
    (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) {e : ℝ}
    (htail : (∑ d ∈ Finset.Ico k N, τ d) ≤ e)
    (hpath : E.pathDisplacement k v (E.map k v x) ≤ e)
    (hterminal : E.terminalDefect N b ≤ e)
    (hdetect : 1 - 2 * e ≤
      f ((E.map k v x : X) - E.evaluate k (E.idealCutoff k x b v))) :
    W.pathWeight k v - 5 * e ≤
      f ((E.beforeBlock h (fun s => E.map N s x) b v : X) -
        E.afterBlock h (fun s => E.map N s x) b v) := by
  exact block_detection_of_norm_bounds f hf
    (E.beforeBlock h (fun s => E.map N s x) b v)
    (E.afterBlock h (fun s => E.map N s x) b v)
    (E.map k v x) (E.evaluate k (E.idealCutoff k x b v))
    (W.pathWeight k v) e hdetect
    (E.beforeBlock_norm_sub_label_le hdiam x b τ h v haverage htail hpath)
    (E.afterBlock_norm_sub_ideal_le x b τ h v haverage htail hterminal)

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.TreeTolerance ----
namespace OAI

/-!
# Tolerances from the actual budgets on the tree

At every positive depth, take the minimum of all budgets at that level and
all earlier positive levels, capped by one.  The cap makes the construction
work for arbitrary positive budgets.  When those budgets are at most one,
the cumulative minimum at every positive depth is attained by an actual
node, so the cap does not change the prescribed finite minimum.

The tolerance is the cumulative minimum multiplied by the dyadic coefficient
`2^(-(k+1))`.  Its value at depth zero is exactly one half.  Every finite tail
is bounded by every actual budget at its initial or an earlier depth.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints
namespace OrderedTree

noncomputable section

variable (T : OrderedTree) (e : (Σ k, T.Node (k + 1)) → ℝ)

theorem levelMinimum_le (k : ℕ) (v : T.Node (k + 1)) :
    T.levelMinimum e k ≤ e ⟨k, v⟩ := by
  exact Finset.inf'_le (fun v => e ⟨k, v⟩) (Finset.mem_univ v)

theorem levelMinimum_pos (he : ∀ v, 0 < e v) (k : ℕ) :
    0 < T.levelMinimum e k := by
  apply (Finset.lt_inf'_iff (T.budgetLevel_nonempty k)).2
  intro v _
  exact he ⟨k, v⟩

theorem cumulativeMinimum_pos (he : ∀ v, 0 < e v) (k : ℕ) :
    0 < T.cumulativeMinimum e k := by
  induction k with
  | zero => norm_num [cumulativeMinimum]
  | succ k ih =>
      exact lt_min ih (T.levelMinimum_pos e he k)

theorem cumulativeMinimum_antitone : Antitone (T.cumulativeMinimum e) := by
  apply antitone_nat_of_succ_le
  intro k
  exact min_le_left _ _

theorem cumulativeMinimum_le_budget {i k : ℕ} (hik : i + 1 ≤ k)
    (v : T.Node (i + 1)) : T.cumulativeMinimum e k ≤ e ⟨i, v⟩ := by
  calc
    T.cumulativeMinimum e k ≤ T.cumulativeMinimum e (i + 1) :=
      T.cumulativeMinimum_antitone e hik
    _ ≤ T.levelMinimum e i := min_le_right _ _
    _ ≤ e ⟨i, v⟩ := T.levelMinimum_le e i v

/-- The unweighted node-budget bound used by the switching construction. -/
theorem tolerance_tail_le_budget (he : ∀ v, 0 < e v)
    {i k N : ℕ} (hik : i + 1 ≤ k) (hkN : k ≤ N) (v : T.Node (i + 1)) :
    (∑ d ∈ Finset.Ico k N, T.tolerance e d) ≤ e ⟨i, v⟩ := by
  exact dyadic_weighted_tail_le_budget (T.cumulativeMinimum e)
    (fun d => (T.cumulativeMinimum_pos e he d).le)
    (T.cumulativeMinimum_antitone e) k N hkN
    (T.cumulativeMinimum_le_budget e hik v)

end
end OrderedTree
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.SwitchingTreeData ----
namespace OAI

/-!
# The concrete tree-construction output consumed by switching

This record states the conclusions of the adaptive ordered-tree producer.
Its candidate labels are the original global selection ordinals. Predictions
are the actual evaluations of the ideal cutoff; the producer derives their
weak limits and detectors from its full earlier-candidate families, with all
discarded candidates retained. No field below is an additional hypothesis of
the public original-norm fixed-point theorem.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace SwitchingTreeData

variable {D : NormalizedMinimalData (X := X)} (A : SwitchingTreeData D)

/-- All extended functionals still have norm at most one. -/
theorem functionalAt_norm (k : ℕ) (v : A.tree.Node k) :
    ‖A.functionalAt k v‖ ≤ 1 := by
  cases k with
  | zero => simp [functionalAt]
  | succ k => exact A.functional_norm k v

end SwitchingTreeData
end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.TreeTerminal ----
namespace OAI

/-!
# Total displacement of the actual finite tree at the terminal sequence

The displacement through depth N is `terminalDefect (N+1)`.
The transmitted-subtree estimate only needs the internal part through depth
N-1.  Both are finite sums of actual generated-map displacements.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace ReflexiveFixedPoints
namespace TreeEvaluation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Including the terminal level can only increase total displacement. -/
theorem terminalDefect_le_succ {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {T : OrderedTree} {W : WeightedTree T} {K : Set X}
    (E : TreeEvaluation W K) (N : ℕ) (b : K) :
    E.terminalDefect N b ≤ E.terminalDefect (N + 1) b := by
  rw [terminalDefect, terminalDefect, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.TreeFiniteWitness ----
namespace OAI

/-!
# Finite witnesses from the actual constructed tree

The construction discharges the terminal, subtree, path, detector, and weighted
budget hypotheses of the finite switching argument using the actual tree data.
It keeps the chosen vector in the entire original-norm difference ball.
-/

noncomputable section

open Filter
open scoped Topology BigOperators Pointwise

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {D : NormalizedMinimalData (X := X)}

namespace SwitchingTreeData

variable (A : SwitchingTreeData D)

/-- All of the actual finite tree's block detector inequalities hold at the
same selected terminal point. -/
theorem finite_block_detection (N j : ℕ)
    (hdet : ∀ v : A.tree.TruncationNode N,
      1 - 2 * A.budget (v.1.val + 1) v.2 ≤
        A.functionalAt (v.1.val + 1) v.2
          ((A.nodeLabel (v.1.val + 1) v.2 : X) -
            A.evaluation.evaluate (v.1.val + 1)
              (A.evaluation.idealCutoff (v.1.val + 1) A.anchor (A.terminal j) v.2)))
    (hD : A.evaluation.terminalDefect (N + 1) (A.terminal j) ≤
      A.tree.cumulativeMinimum (OrderedTree.retainedBudget A.label) N)
    (v : A.tree.TruncationNode N) :
    A.weights.pathWeight (v.1.val + 1) v.2 - 5 * A.budget (v.1.val + 1) v.2 ≤
      A.functionalAt (v.1.val + 1) v.2
        ((A.evaluation.beforeBlock v.levelBound (A.nodeLabel N) (A.terminal j) v.2 : X) -
          A.evaluation.afterBlock v.levelBound (A.nodeLabel N) (A.terminal j) v.2) := by
  have htail : (∑ d ∈ Finset.Ico (v.1.val + 1) N,
      A.tree.tolerance (OrderedTree.retainedBudget A.label) d) ≤
        A.budget (v.1.val + 1) v.2 :=
    A.tree.tolerance_tail_le_budget (OrderedTree.retainedBudget A.label)
      (OrderedTree.retainedBudget_pos A.label) (Nat.le_refl _) v.levelBound v.2
  have hterminal : A.evaluation.terminalDefect N (A.terminal j) ≤
      A.budget (v.1.val + 1) v.2 :=
    (A.evaluation.terminalDefect_le_succ N (A.terminal j)).trans
      (hD.trans (A.tree.cumulativeMinimum_le_budget
        (OrderedTree.retainedBudget A.label) v.levelBound v.2))
  exact A.evaluation.actual_block_detection D.norm_sub_le_one A.anchor (A.terminal j)
    (A.tree.tolerance (OrderedTree.retainedBudget A.label)) v.levelBound v.2
    (fun d _ p => A.child_average d p) (A.functionalAt (v.1.val + 1) v.2)
    (A.functionalAt_norm _ _) htail (A.path_displacement _ _) hterminal (hdet v)

end SwitchingTreeData
end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.SwitchingTreeData
open Filter
open scoped Topology BigOperators Pointwise


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.SwitchingTreeData.finite_block_detection := @_root_.OAI.ReflexiveFixedPoints.SwitchingTreeData.finite_block_detection
