-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.tree_finite_witnesses_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T18:22:09.463267+00:00
-- url     : https://prove2.me/submissions/bad1a201-f8ff-40ab-a641-f7795a162d88

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/BranchContradiction.lean:L43-L110
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.tree_finite_witnesses_contradiction. The node keeps its source
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
import Theorems.Thm_OAI_ReflexiveFixedPoints_OrderedTree_exists_feasible_branch
import Theorems.Thm_OAI_ReflexiveFixedPoints_abs_apply_sub_le_of_detector
import Theorems.Thm_OAI_ReflexiveFixedPoints_exists_weaklyCompact_all_halfspaces
import Theorems.Thm_OAI_ReflexiveFixedPoints_pairwiseDifferences_subset_closure
import Theorems.Thm_OAI_ReflexiveFixedPoints_tendsto_zero_of_mem_closedSpan

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

theorem detectsPrefix_zero (v : T.Node 0) (d : D) :
    T.DetectsPrefix f v d := by
  intro i hi hpos
  exact False.elim ((Nat.not_lt_of_ge hi) hpos)

theorem feasible_zero (hB : B.Nonempty) (v : T.Node 0) :
    T.Feasible B f v := by
  obtain ⟨d, hd⟩ := hB
  exact ⟨d, hd, T.detectsPrefix_zero f v d⟩

/-- Prefix feasibility written directly in the coherent branch coordinates. -/
theorem exists_feasible_branch_with_witnesses
    (hne : ∀ n, ∃ v : T.Node n, T.Feasible B f v) :
    ∃ b : (n : ℕ) → T.Node n,
      T.IsBranch b ∧
      ∀ n, ∃ d ∈ B, ∀ i, 0 < i → i ≤ n →
        (1 / 2 : ℝ) ≤ f i (b i) d := by
  obtain ⟨b, hb, hfeasible⟩ := T.exists_feasible_branch B f hne
  refine ⟨b, hb, ?_⟩
  intro n
  obtain ⟨d, hdB, hd⟩ := hfeasible n
  refine ⟨d, hdB, ?_⟩
  intro i hpos hin
  have hi := hd i hin hpos
  rw [hb hin] at hi
  exact hi

/-- The positive-depth finite witness theorem suffices; depth zero uses any element of B. -/
theorem exists_branch_of_finite_witnesses (hB : B.Nonempty)
    (hfinite : ∀ n, 0 < n → ∃ v : T.Node n,
      ∃ d ∈ B, T.DetectsPrefix f v d) :
    ∃ b : (n : ℕ) → T.Node n,
      T.IsBranch b ∧
      ∀ n, ∃ d ∈ B, ∀ i, 0 < i → i ≤ n →
        (1 / 2 : ℝ) ≤ f i (b i) d := by
  apply T.exists_feasible_branch_with_witnesses B f
  intro n
  cases n with
  | zero => exact ⟨T.root, T.feasible_zero B f hB T.root⟩
  | succ n => exact hfinite (n + 1) (Nat.succ_pos n)

end OrderedTree
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.DenseDifferences ----
namespace OAI

/-!
# Dense pairwise differences in the norm-closed difference span

All closures use the given norm topology. Density in the norm subtype of `K`
is transported through the continuous subtraction map on `K × K`.
No completeness, convexity, closedness or compactness assumption is needed.
-/

open scoped Pointwise

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {K : Set X}

theorem pairwiseDifferences_subset_sub {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {K : Set X} (z : ℕ → K) :
    Set.range (fun ij : ℕ × ℕ => (z ij.1 : X) - (z ij.2 : X)) ⊆ K - K := by
  rintro _ ⟨ij, rfl⟩
  exact Set.sub_mem_sub (z ij.1).property (z ij.2).property

/-- The sampled pairwise differences generate the entire norm-closed difference span. -/
theorem closure_span_pairwiseDifferences (z : ℕ → K) (hz : DenseRange z) :
    (Submodule.span ℝ
      (Set.range (fun ij : ℕ × ℕ => (z ij.1 : X) - (z ij.2 : X)))).topologicalClosure =
      (Submodule.span ℝ (K - K)).topologicalClosure := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_mono
      (Submodule.span_mono (pairwiseDifferences_subset_sub z))
  · apply (Submodule.span ℝ (K - K)).topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      exact (pairwiseDifferences_subset_closure z hz).trans
        (Submodule.closure_subset_topologicalClosure_span _)
    · exact Submodule.isClosed_topologicalClosure _

/-- The same equality with the shared reduction carrier. -/
theorem closure_span_pairwiseDifferences_eq_differenceSpan
    (z : ℕ → K) (hz : DenseRange z) :
    (Submodule.span ℝ
      (Set.range (fun ij : ℕ × ℕ => (z ij.1 : X) - (z ij.2 : X)))).topologicalClosure =
      differenceSpan K :=
  closure_span_pairwiseDifferences z hz

end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.FunctionalVanishing ----
namespace OAI

/-!
# Vanishing of uniformly bounded functionals on a closed span

Convergence on the generators extends first by linearity to their span,
then by an explicit epsilon estimate to its norm closure. Summable budgets
also vanish along any injective sequence of their actual indices.
-/

open Filter Topology

namespace ReflexiveFixedPoints

/-- Summable budgets tend to zero along any injective sequence of indices. -/
theorem summable_budget_tendsto {I : Type*}
    (e : I → ℝ) (he : Summable e)
    (b : ℕ → I) (hb : Function.Injective b) :
    Tendsto (fun n => e (b n)) atTop (𝓝 0) :=
  (he.comp_injective hb).tendsto_atTop_zero

end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.BranchContradiction ----
namespace OAI

/-!
# The branch contradiction from the actual finite witnesses

The actual ordered tree supplies detector labels and summable budgets. The
finite switching witnesses give a feasible branch. Weak compactness of the
whole difference ball keeps one common vector, whereas the same detectors
vanish on its closed difference span by density and their uniform norm bound.
-/

open Filter Topology

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The precise outputs of the tree and finite switching construction cannot
coexist in the normalized minimal data. Every listed input is supplied by an
earlier concrete producer; no branch or pointwise-vanishing premise is used. -/
theorem tree_finite_witnesses_contradiction
    (D : NormalizedMinimalData (X := X)) (T : OrderedTree)
    (f : (k : ℕ) → T.Node k → (X →L[ℝ] ℝ))
    (y : (k : ℕ) → T.Node k → D.K)
    (e : (k : ℕ) → T.Node k → ℝ)
    (hnorm : ∀ k, 0 < k → ∀ v : T.Node k, ‖f k v‖ ≤ 1)
    (hdetector : ∀ k, 0 < k → ∀ v : T.Node k, ∀ i, i < k →
      1 - e k v ≤ f k v ((y k v : X) - (D.z i : X)))
    (hbudget : Summable (fun v : Σ k, T.Node (k + 1) => e (v.1 + 1) v.2))
    (hfinite : ∀ n, 0 < n → ∃ v : T.Node n,
      ∃ d ∈ differenceBall D.K,
        T.DetectsPrefix (fun k v x => f k v x) v d) :
    False := by
  have hB : (differenceBall D.K).Nonempty := by
    refine ⟨0, ?_⟩
    change 0 ∈ differenceSpan D.K ∧ ‖(0 : X)‖ ≤ 1
    exact ⟨(differenceSpan D.K).zero_mem, by simp⟩
  obtain ⟨b, _hbranch, hprefix⟩ :=
    T.exists_branch_of_finite_witnesses (differenceBall D.K)
      (fun k v x => f k v x) hB hfinite
  let φ : ℕ → X →L[ℝ] ℝ := fun n => f (n + 1) (b (n + 1))
  have hφ (n : ℕ) : ‖φ n‖ ≤ 1 := hnorm (n + 1) (Nat.succ_pos n) _
  have hprefixφ : ∀ n : ℕ, ∃ d ∈ differenceBall D.K,
      ∀ i < n, (1 / 2 : ℝ) ≤ φ i d := by
    intro n
    obtain ⟨d, hdB, hd⟩ := hprefix n
    refine ⟨d, hdB, ?_⟩
    intro i hi
    exact hd (i + 1) (Nat.succ_pos i) (Nat.succ_le_of_lt hi)
  obtain ⟨d, hdB, hlarge⟩ := exists_weaklyCompact_all_halfspaces
    (differenceBall D.K) D.weak_ball_compact φ (1 / 2) hprefixφ
  let branchIndex : ℕ → Σ k, T.Node (k + 1) := fun n => ⟨n, b (n + 1)⟩
  have hbranchIndex : Function.Injective branchIndex := by
    intro i j hij
    exact congrArg (fun v : Σ k, T.Node (k + 1) => v.1) hij
  have hezero : Tendsto (fun n => e (n + 1) (b (n + 1))) atTop (𝓝 0) :=
    summable_budget_tendsto
      (fun v : Σ k, T.Node (k + 1) => e (v.1 + 1) v.2)
      hbudget branchIndex hbranchIndex
  have hpair (i j : ℕ) :
      Tendsto (fun n => φ n ((D.z i : X) - (D.z j : X))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n => e (n + 1) (b (n + 1))) _ hezero
    refine Filter.eventually_atTop.mpr ⟨max i j, ?_⟩
    intro n hn
    have hi : i < n + 1 := Nat.lt_succ_of_le ((le_max_left i j).trans hn)
    have hj : j < n + 1 := Nat.lt_succ_of_le ((le_max_right i j).trans hn)
    have h := abs_apply_sub_le_of_detector (φ n) (hφ n)
      (y (n + 1) (b (n + 1))) (D.z i) (D.z j) (e (n + 1) (b (n + 1)))
      (D.norm_sub_le_one _ _) (D.norm_sub_le_one _ _)
      (hdetector (n + 1) (Nat.succ_pos n) _ i hi)
      (hdetector (n + 1) (Nat.succ_pos n) _ j hj)
    simpa only [Real.norm_eq_abs] using h
  have hzero : Tendsto (fun n => φ n d) atTop (𝓝 0) := by
    apply tendsto_zero_of_mem_closedSpan φ hφ
      (s := Set.range (fun ij : ℕ × ℕ => (D.z ij.1 : X) - (D.z ij.2 : X)))
    · rintro x ⟨⟨i, j⟩, rfl⟩
      exact hpair i j
    · rw [closure_span_pairwiseDifferences_eq_differenceSpan D.z D.dense_z]
      exact hdB.1
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hzero (1 / 4) (by linarith)
  have hsmall : |φ N d| < 1 / 4 := by
    simpa only [Real.dist_eq, sub_zero] using hN N le_rfl
  have hlargeN := hlarge N
  have habs := le_abs_self (φ N d)
  linarith

end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints
open Filter Topology


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.tree_finite_witnesses_contradiction := @_root_.OAI.ReflexiveFixedPoints.tree_finite_witnesses_contradiction
