-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T18:24:20.103837+00:00
-- url     : https://prove2.me/submissions/7bc543e9-ca37-4f0b-bcbf-ad7665735520

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/Main.lean:L38-L48
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ReflexiveFixedPoints_exists_fixedPoint_of_canonicallyReflexive) verbatim and is proved by it.
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
import Theorems.Thm_OAI_ReflexiveFixedPoints_SwitchingTreeData_exists_finite_terminal
import Theorems.Thm_OAI_ReflexiveFixedPoints_SwitchingTreeData_finite_block_detection
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_finite_witness_of_block_detection
import Theorems.Thm_OAI_ReflexiveFixedPoints_exists_normalizedMinimalData_of_counterexample
import Theorems.Thm_OAI_ReflexiveFixedPoints_tree_finite_witnesses_contradiction

-- ---- from OAI.Analysis.Nonexpansive.OriginalNorm ----
namespace OAI

/-!
# The fixed point property in the given norm

The public property quantifies over actual convex subsets and their selfmaps.
Its nonexpansiveness condition uses the existing ambient norm.  These elementary
interface lemmas neither change that norm nor supply the main reflexive-space
theorem; the latter is proved by the reduction and contradiction chain.
-/

noncomputable section

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem nonexpansiveOn_iff_lipschitzWith_one {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (C : Set X) (F : C → C) :
    NonexpansiveOn C F ↔ LipschitzWith 1 F := by
  constructor
  · intro h
    apply LipschitzWith.mk_one
    intro a b
    simpa only [Subtype.dist_eq, dist_eq_norm] using h a b
  · intro h a b
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
      using h.dist_le_mul a b

end ReflexiveFixedPoints

end

end OAI

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

theorem candidateBudget_nonneg (n : ℕ) : 0 ≤ candidateBudget n :=
  (candidateBudget_pos n).le

/-- The complete candidate series has sum exactly `1 / 256`. -/
theorem hasSum_candidateBudget : HasSum candidateBudget (1 / 256 : ℝ) := by
  have h := HasSum.mul_right ((1 / 2 : ℝ) ^ 9) hasSum_geometric_two
  change HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 9)) (1 / 256 : ℝ)
  simpa only [candidateBudget, pow_add] using
    (show HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ 9)
      (1 / 256 : ℝ) from by convert! h using 1; norm_num)

theorem summable_candidateBudget : Summable candidateBudget :=
  hasSum_candidateBudget.summable

theorem tsum_candidateBudget : (∑' n, candidateBudget n) = (1 / 256 : ℝ) :=
  hasSum_candidateBudget.tsum_eq

namespace OrderedTree

variable {T : OrderedTree}

theorem retainedBudget_pos (label : T.NonrootNode → ℕ) (v : T.NonrootNode) :
    0 < retainedBudget label v :=
  candidateBudget_pos (label v)

theorem retainedBudget_nonneg (label : T.NonrootNode → ℕ) (v : T.NonrootNode) :
    0 ≤ retainedBudget label v :=
  (retainedBudget_pos label v).le

/-- Retaining a subset of globally distinct candidate labels preserves
summability.  No bound on the number of nodes at later levels is needed. -/
theorem summable_retainedBudget (label : T.NonrootNode → ℕ)
    (hlabel : Function.Injective label) : Summable (retainedBudget label) := by
  exact summable_candidateBudget.comp_injective hlabel

/-- The total retained budget is at most the complete candidate budget. -/
theorem tsum_retainedBudget_le (label : T.NonrootNode → ℕ)
    (hlabel : Function.Injective label) :
    (∑' v, retainedBudget label v) ≤ (1 / 256 : ℝ) := by
  calc
    (∑' v, retainedBudget label v) ≤ ∑' n, candidateBudget n := by
      exact tsum_comp_le_tsum_of_inj summable_candidateBudget candidateBudget_nonneg hlabel
    _ = (1 / 256 : ℝ) := tsum_candidateBudget

/-- A finite truncation, or any finite injectively indexed collection of
actual nonroot nodes, satisfies the complete retained budget bound. -/
theorem sum_retainedBudget_comp_le {ι : Type*} [Fintype ι]
    (label : T.NonrootNode → ℕ) (hlabel : Function.Injective label)
    (node : ι → T.NonrootNode) (hnode : Function.Injective node) :
    (∑ i, retainedBudget label (node i)) ≤ (1 / 256 : ℝ) := by
  calc
    (∑ i, retainedBudget label (node i)) = ∑' i, retainedBudget label (node i) :=
      (tsum_fintype _).symm
    _ ≤ ∑' v, retainedBudget label v :=
      tsum_comp_le_tsum_of_inj (summable_retainedBudget label hlabel)
        (retainedBudget_nonneg label) hnode
    _ ≤ (1 / 256 : ℝ) := tsum_retainedBudget_le label hlabel

end OrderedTree
end ReflexiveFixedPoints

end

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

theorem summable_budget :
    Summable (fun v : A.tree.NonrootNode => A.budget (v.1 + 1) v.2) :=
  OrderedTree.summable_retainedBudget A.label A.label_injective

end SwitchingTreeData
end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.TreeProducer ----
namespace OAI

/-!
# The actual adaptive ordered tree

The anchor is produced by the resolvent-tail construction. A fixed ultrafilter
refines the ordinary tail filter. Concrete finite candidate selections then
construct each level, keeping every discarded candidate in its history. The
finite-frontier recursion produces the final tree and all its detector,
weight, return, path, and ideal-prediction conclusions.
-/

noncomputable section

open Filter

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The tree, its anchor and all central construction laws are produced
from the actual normalized minimal invariant set. -/
theorem exists_switchingTreeData (D : NormalizedMinimalData (X := X)) :
    Nonempty (SwitchingTreeData D) := by
  let A := resolventAnchorPoint D.nonempty D.closed D.convex D.T
    D.nonexpansive D.weak_compact
  let U := Ultrafilter.of (Filter.atTop : Filter ℕ)
  exact ⟨switchingTreeDataOfAnchor D A U (Ultrafilter.of_le (Filter.atTop : Filter ℕ))⟩

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

theorem truncationEmbedding_injective (N : ℕ) :
    Function.Injective (A.truncationEmbedding N) := by
  rintro ⟨⟨i, hi⟩, v⟩ ⟨⟨j, hj⟩, w⟩ h
  change (⟨i, v⟩ : A.tree.NonrootNode) = ⟨j, w⟩ at h
  obtain ⟨hij, hvw⟩ := Sigma.mk.inj_iff.mp h
  subst j
  have hvw' : v = w := eq_of_heq hvw
  subst w
  rfl

/-- Every finite truncation uses its original retained candidate budgets. -/
theorem finite_budget_le (N : ℕ) :
    (∑ v : A.tree.TruncationNode N, A.budget (v.1.val + 1) v.2) ≤
      (1 : ℝ) / 128 := by
  have h := OrderedTree.sum_retainedBudget_comp_le A.label A.label_injective
    (A.truncationEmbedding N) (A.truncationEmbedding_injective N)
  exact h.trans (by norm_num)

/-- The actual normalized differences lie in the original difference span. -/
theorem difference_mem_span (_A : SwitchingTreeData D) (a b : D.K) :
    (a : X) - b ∈ differenceSpan D.K := by
  apply (Submodule.span ℝ (D.K - D.K)).le_topologicalClosure
  exact Submodule.subset_span (Set.sub_mem_sub a.property b.property)

/-- The constructed infinite tree has a whole-ball witness at every finite
depth.  Every central switching estimate has been discharged above. -/
theorem finite_witness (N : ℕ) :
    ∃ v : A.tree.Node N, ∃ d ∈ differenceBall D.K,
      A.tree.DetectsPrefix (fun k v x => A.functionalAt k v x) v d := by
  obtain ⟨j, hdet, hD⟩ := A.exists_finite_terminal N
  obtain ⟨s, hsY, hsNorm, hsDetect⟩ :=
    A.evaluation.finite_witness_of_block_detection N (A.nodeLabel N) (A.terminal j)
      (differenceSpan D.K) (A.difference_mem_span) D.norm_sub_le_one
      A.functionalAt A.functionalAt_norm
      (fun v => A.budget (v.1.val + 1) v.2) (A.finite_budget_le N)
      (A.finite_block_detection N j hdet hD)
  refine ⟨s, A.evaluation.switchVector N (A.nodeLabel N) (A.terminal j) s,
    ⟨hsY, hsNorm⟩, ?_⟩
  exact hsDetect

end SwitchingTreeData
end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.NormalizedContradiction ----
namespace OAI

/-!
# The actual tree and switching contradiction for normalized minimal data

The adaptive producer constructs the tree without an added geometric premise.
Its actual finite switching witnesses lie in the whole difference ball, and
the branch argument contradicts the produced dense-point detectors there.
-/

noncomputable section

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace SwitchingTreeData

/-- The concrete constructed tree cannot coexist with normalized minimal data. -/
theorem contradiction {D : NormalizedMinimalData (X := X)} (A : SwitchingTreeData D) :
    False := by
  apply tree_finite_witnesses_contradiction D A.tree A.functionalAt A.nodeLabel A.budget
  · intro k hk v
    exact A.functionalAt_norm k v
  · intro k hk v i hi
    cases k with
    | zero => omega
    | succ k => exact A.dense_detector k v i hi
  · exact A.summable_budget
  · intro n hn
    exact A.finite_witness n

end SwitchingTreeData

/-- No normalized minimal invariant counterexample exists. This calls the
actual adaptive-tree producer and the fully discharged finite switching proof. -/
theorem normalizedMinimalData_false (D : NormalizedMinimalData (X := X)) : False := by
  obtain ⟨A⟩ := exists_switchingTreeData D
  exact A.contradiction

end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.Main ----
namespace OAI

/-!
# Fixed points in the original norm

The counterexample reduction constructs the actual normalized minimal data.
The adaptive tree, finite switching witnesses and whole-ball branch argument
then contradict those data.  The public statements use the given norm on the
original real Banach space, including the zero and nonseparable cases.
-/

noncomputable section

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A real reflexive Banach space has the nonexpansive fixed point property
in its given norm. Reflexivity is canonical continuous-bidual surjectivity. -/
theorem hasNonexpansiveFixedPointProperty_of_canonicallyReflexive
    (hX : CanonicallyReflexive X) : HasNonexpansiveFixedPointProperty X := by
  intro C hne hclosed hbounded hconvex F hF
  by_contra hnone
  have hno : ∀ x : C, F x ≠ x := by
    intro x hx
    exact hnone ⟨x, hx⟩
  obtain ⟨D⟩ := exists_normalizedMinimalData_of_counterexample
    hX hne hclosed hbounded hconvex F
    ((nonexpansiveOn_iff_lipschitzWith_one C F).mp hF) hno
  exact normalizedMinimalData_false D

/-- Every nonexpansive selfmap of a nonempty closed bounded convex set has
an actual fixed point, with nonexpansiveness stated in the original norm. -/
theorem exists_fixedPoint_of_canonicallyReflexive
    (hX : CanonicallyReflexive X) (C : Set X)
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C)
    (hF : ∀ a b : C, ‖(F a : X) - (F b : X)‖ ≤ ‖(a : X) - (b : X)‖) :
    ∃ a : C, F a = a :=
  hasNonexpansiveFixedPointProperty_of_canonicallyReflexive hX
    C hne hclosed hbounded hconvex F hF

end ReflexiveFixedPoints

end

end OAI

-- ---- mission target ----
open OAI OAI.ReflexiveFixedPoints
universe u
variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {X}

namespace OAI
namespace ReflexiveFixedPoints
theorem _root_.solution
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : CanonicallyReflexive X) (C : Set X)
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C)
    (hF : ∀ a b : C, ‖(F a : X) - (F b : X)‖ ≤ ‖(a : X) - (b : X)‖) :
    ∃ a : C, F a = a := by
  first
    | exact OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive hX C hne hclosed hbounded hconvex F hF
    | exact OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive X hX C hne hclosed hbounded hconvex F hF
    | exact OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive
    | (apply OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive <;> assumption)
    | (intros; apply OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive <;> assumption)
end ReflexiveFixedPoints
end OAI
