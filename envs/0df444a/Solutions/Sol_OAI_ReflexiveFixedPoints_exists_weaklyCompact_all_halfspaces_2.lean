-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.exists_weaklyCompact_all_halfspaces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T18:16:58.099984+00:00
-- url     : https://prove2.me/submissions/9c443bf6-649c-465e-a999-a562b6cca59a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/WeakBranchIntersection.lean:L19-L48
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.exists_weaklyCompact_all_halfspaces. The node keeps its source
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

-- ---- from OAI.Analysis.Nonexpansive.WeakBranchIntersection ----
namespace OAI

/-!
# One vector satisfying every branch halfspace

The finite-prefix witnesses lie in the same actual weakly compact set.
Continuous linear evaluations define weakly closed halfspaces. Compactness
then keeps one vector in all the constraints. In the final application the
set is the whole unit ball of the closed difference span, viewed in X.
-/

namespace ReflexiveFixedPoints

/-- Finite-prefix feasibility in an actual weakly compact set gives one point
in every halfspace. Only scalar linear evaluations use weak continuity. -/
theorem exists_weaklyCompact_all_halfspaces
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : Set X) (hB : WeaklyCompact B)
    (f : ℕ → X →L[ℝ] ℝ) (c : ℝ)
    (hPrefix : ∀ n : ℕ, ∃ x ∈ B, ∀ i < n, c ≤ f i x) :
    ∃ x ∈ B, ∀ i, c ≤ f i x := by
  classical
  let H : ℕ → Set (WeakSpace ℝ X) :=
    fun i => {w | c ≤ f i ((toWeakSpace ℝ X).symm w)}
  have hclosed (i : ℕ) : IsClosed (H i) :=
    isClosed_le continuous_const
      (WeakBilin.eval_continuous (topDualPairing ℝ X).flip (f i))
  have hfinite (s : Finset ℕ) :
      (((toWeakSpace ℝ X) '' B) ∩ ⋂ i ∈ s, H i).Nonempty := by
    obtain ⟨x, hx, hfx⟩ := hPrefix (s.sup id + 1)
    refine ⟨toWeakSpace ℝ X x, ⟨x, hx, rfl⟩, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    change c ≤ f i ((toWeakSpace ℝ X).symm (toWeakSpace ℝ X x))
    simpa only [LinearEquiv.symm_apply_apply] using
      hfx i (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have hcompact : IsCompact ((toWeakSpace ℝ X) '' B) := hB
  obtain ⟨w, hwB, hwH⟩ := hcompact.inter_iInter_nonempty H hclosed hfinite
  obtain ⟨x, hx, rfl⟩ := hwB
  refine ⟨x, hx, ?_⟩
  intro i
  have hi := Set.mem_iInter.mp hwH i
  simpa only [H, Set.mem_ofPred_eq, LinearEquiv.symm_apply_apply] using hi

end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.exists_weaklyCompact_all_halfspaces := @_root_.OAI.ReflexiveFixedPoints.exists_weaklyCompact_all_halfspaces
