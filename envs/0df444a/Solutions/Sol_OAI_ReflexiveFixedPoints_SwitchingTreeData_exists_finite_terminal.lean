-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.SwitchingTreeData.exists_finite_terminal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T18:07:22.496685+00:00
-- url     : https://prove2.me/submissions/66f1b185-9dbb-488b-a485-070099c8e8d4

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/TreeFiniteWitness.lean:L53-L94
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.SwitchingTreeData.exists_finite_terminal. The node keeps its source
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
import Theorems.Thm_OAI_ReflexiveFixedPoints_common_terminal_of_tendsto

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

-- ---- from OAI.Analysis.Nonexpansive.TerminalSequence ----
namespace OAI

/-!
# One common terminal sequence for all fixed generated maps

The terminal sequence uses zero-based indices. All quantitative estimates
retain the denominator `j+1`.
The sequence is constructed once. Every fixed finite family of generated
maps has total displacement tending to zero along this same sequence.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace ReflexiveFixedPoints

universe u v

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {K : Set X}

theorem terminalSequence_defect_le (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1) (x : K) (j : ℕ) :
    ‖(T (terminalSequence hKclosed hKconvex T hT x j) : X) -
      (terminalSequence hKclosed hKconvex T hT x j : X)‖ ≤ 1 / ((j : ℝ) + 1) := by
  simpa only [terminalSequence, Nat.cast_add, Nat.cast_one] using
    resolvent_defect_le hKclosed hKconvex T hT hdiam (j + 1)
      (Nat.succ_le_succ (Nat.zero_le j)) x

theorem terminalSequence_defect_tendsto (hKclosed : IsClosed K)
    (hKconvex : Convex ℝ K) (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1) (x : K) :
    Tendsto (fun j : ℕ =>
      ‖(T (terminalSequence hKclosed hKconvex T hT x j) : X) -
        (terminalSequence hKclosed hKconvex T hT x j : X)‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _)
    (terminalSequence_defect_le hKclosed hKconvex T hT hdiam x)
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem terminalSequence_generated_displacement_tendsto
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    {G : K → K} (hG : Generated hKclosed hKconvex T hT G) (x : K) :
    Tendsto (fun j : ℕ =>
      ‖(G (terminalSequence hKclosed hKconvex T hT x j) : X) -
        (terminalSequence hKclosed hKconvex T hT x j : X)‖) atTop (𝓝 0) := by
  obtain ⟨c, hc, hbound⟩ := generated_displacement hG
  have hlim : Tendsto (fun j : ℕ =>
      c * ‖(T (terminalSequence hKclosed hKconvex T hT x j) : X) -
        (terminalSequence hKclosed hKconvex T hT x j : X)‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (terminalSequence_defect_tendsto hKclosed hKconvex T hT hdiam x)
  exact squeeze_zero (fun _ => norm_nonneg _) (fun j => hbound _) hlim

theorem terminalSequence_finite_displacement_tendsto
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (T : K → K) (hT : LipschitzWith 1 T)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    {ι : Type v} [Fintype ι] (G : ι → K → K)
    (hG : ∀ i, Generated hKclosed hKconvex T hT (G i)) (x : K) :
    Tendsto (fun j : ℕ => ∑ i,
      ‖(G i (terminalSequence hKclosed hKconvex T hT x j) : X) -
        (terminalSequence hKclosed hKconvex T hT x j : X)‖) atTop (𝓝 0) := by
  have hlim := tendsto_finsetSum Finset.univ fun i _ =>
    terminalSequence_generated_displacement_tendsto hKclosed hKconvex T hT hdiam (hG i) x
  simpa only [Finset.sum_const_zero] using hlim

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

theorem budget_pos (k : ℕ) (v : A.tree.Node (k + 1)) :
    0 < A.budget (k + 1) v :=
  OrderedTree.retainedBudget_pos A.label ⟨k, v⟩

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

/-- The total displacement of every fixed finite actual tree tends to zero on
its one common resolvent terminal sequence. -/
theorem terminalDefect_terminalSequence_tendsto
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (F : K → K) (hF : LipschitzWith 1 F)
    (hdiam : ∀ a b : K, ‖(a : X) - b‖ ≤ 1)
    (hgenerated : ∀ k v, Generated hKclosed hKconvex F hF (E.map k v))
    (x : K) (N : ℕ) :
    Tendsto (fun j => E.terminalDefect N (terminalSequence hKclosed hKconvex F hF x j))
      atTop (𝓝 0) := by
  have hlim := tendsto_finsetSum (Finset.range N) fun k _ =>
    terminalSequence_finite_displacement_tendsto hKclosed hKconvex F hF hdiam
      (E.map k) (hgenerated k) x
  simpa only [terminalDefect, Finset.sum_const_zero] using hlim

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.CommonTerminal ----
namespace OAI

/-!
# A common terminal index for finitely many detectors

This finite-filter argument chooses one actual index at which all scalar
prediction detectors and the total displacement bound hold.  Its applications
supply the scalar limits by evaluating continuous linear functionals on the
actual weak prediction limits, and supply displacement convergence for the
actual finite collection of node maps.
-/

noncomputable section

open Filter
open scoped Topology

namespace ReflexiveFixedPoints

/-- The displacement may converge in a larger filter, in particular the
cofinite filter contained in a fixed free ultrafilter. -/
theorem common_terminal_of_tendsto_mono
    {I J : Type*} [Finite I] {l l' : Filter J} [NeBot l]
    (hll' : l ≤ l')
    (e a : I → ℝ) (g : I → J → ℝ) (D : J → ℝ) (M : ℝ)
    (he : ∀ i, 0 < e i)
    (ha : ∀ i, 1 - e i ≤ a i)
    (hg : ∀ i, Tendsto (g i) l (𝓝 (a i)))
    (hD : Tendsto D l' (𝓝 0)) (hM : 0 < M) :
    ∃ j, (∀ i, 1 - 2 * e i ≤ g i j) ∧ D j ≤ M :=
  common_terminal_of_tendsto e a g D M he ha hg (hD.mono_left hll') hM

end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.WeakCommonTerminal ----
namespace OAI

/-!
# A common actual resolvent terminal for weak prediction detectors

The scalar convergence is derived from weak convergence of the fully evaluated
predictions.  The displacement convergence is the proved estimate for the actual
resolvent terminal sequence and actual generated maps.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {K : Set X}

/-- A continuous linear functional converts an actual weak prediction limit to
the scalar detector limit.  No weak continuity of a nonlinear map is used. -/
theorem detector_tendsto_of_weak_tendsto {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {J : Type*} {l : Filter J} (f : X →L[ℝ] ℝ) (y z : X) (q : J → X)
    (hq : Tendsto (fun j => toWeakSpace ℝ X (q j)) l
      (𝓝 (toWeakSpace ℝ X z))) :
    Tendsto (fun j => f (y - q j)) l (𝓝 (f (y - z))) := by
  have hcont : Continuous (fun w : WeakSpace ℝ X => f ((toWeakSpace ℝ X).symm w)) :=
    WeakBilin.eval_continuous (topDualPairing ℝ X).flip f
  have heval := hcont.continuousAt.tendsto.comp hq
  simpa only [LinearEquiv.symm_apply_apply, map_sub] using
    (tendsto_const_nhds.sub heval :
      Tendsto (fun j => f y - f ((toWeakSpace ℝ X).symm (toWeakSpace ℝ X (q j)))) l
        (𝓝 (f y - f ((toWeakSpace ℝ X).symm (toWeakSpace ℝ X z)))))

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

/-- One actual terminal resolvent satisfies every finite prediction detector
and the full displacement sum through the terminal level. -/
theorem exists_finite_terminal (N : ℕ) :
    ∃ j,
      (∀ v : A.tree.TruncationNode N,
        1 - 2 * A.budget (v.1.val + 1) v.2 ≤
          A.functionalAt (v.1.val + 1) v.2
            ((A.nodeLabel (v.1.val + 1) v.2 : X) -
              A.evaluation.evaluate (v.1.val + 1)
                (A.evaluation.idealCutoff (v.1.val + 1) A.anchor (A.terminal j) v.2))) ∧
      A.evaluation.terminalDefect (N + 1) (A.terminal j) ≤
        A.tree.cumulativeMinimum (OrderedTree.retainedBudget A.label) N := by
  let e : A.tree.TruncationNode N → ℝ :=
    fun v => A.budget (v.1.val + 1) v.2
  let a : A.tree.TruncationNode N → ℝ := fun v =>
    A.functional v.1.val v.2
      ((A.nodeLabel (v.1.val + 1) v.2 : X) - A.predictionLimit v.1.val v.2)
  let g : A.tree.TruncationNode N → ℕ → ℝ := fun v j =>
    A.functional v.1.val v.2
      ((A.nodeLabel (v.1.val + 1) v.2 : X) -
        A.evaluation.evaluate (v.1.val + 1)
          (A.evaluation.idealCutoff (v.1.val + 1) A.anchor (A.terminal j) v.2))
  have he : ∀ v, 0 < e v := fun v => A.budget_pos _ _
  have ha : ∀ v, 1 - e v ≤ a v := fun v => A.prediction_detector _ _
  have hg : ∀ v, Tendsto (g v) (A.ultrafilter : Filter ℕ) (𝓝 (a v)) := by
    intro v
    exact detector_tendsto_of_weak_tendsto (A.functional v.1.val v.2)
      (A.nodeLabel (v.1.val + 1) v.2) (A.predictionLimit v.1.val v.2)
      (fun j => A.evaluation.evaluate (v.1.val + 1)
        (A.evaluation.idealCutoff (v.1.val + 1) A.anchor (A.terminal j) v.2))
      (A.prediction_tendsto _ _)
  have hD : Tendsto (fun j => A.evaluation.terminalDefect (N + 1) (A.terminal j))
      atTop (𝓝 0) :=
    A.evaluation.terminalDefect_terminalSequence_tendsto D.closed D.convex D.T
      D.nonexpansive D.norm_sub_le_one A.generated A.anchor (N + 1)
  have hM : 0 < A.tree.cumulativeMinimum (OrderedTree.retainedBudget A.label) N :=
    A.tree.cumulativeMinimum_pos (OrderedTree.retainedBudget A.label)
      (OrderedTree.retainedBudget_pos A.label) N
  exact common_terminal_of_tendsto_mono A.ultrafilter_le_atTop e a g
    (fun j => A.evaluation.terminalDefect (N + 1) (A.terminal j))
    (A.tree.cumulativeMinimum (OrderedTree.retainedBudget A.label) N)
    he ha hg hD hM

end SwitchingTreeData
end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.SwitchingTreeData
open Filter
open scoped Topology BigOperators Pointwise


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.SwitchingTreeData.exists_finite_terminal := @_root_.OAI.ReflexiveFixedPoints.SwitchingTreeData.exists_finite_terminal
