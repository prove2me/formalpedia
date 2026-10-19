-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.tendsto_zero_of_mem_closedSpan
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T18:15:14.589778+00:00
-- url     : https://prove2.me/submissions/5e34e75d-714f-4606-b2c3-4ebbc6051bc0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/FunctionalVanishing.lean:L20-L55
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.tendsto_zero_of_mem_closedSpan. The node keeps its source
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

/-- A sequence of functionals of norm at most one that tends to zero on a
set of generators tends to zero at each point of their closed linear span. -/
theorem tendsto_zero_of_mem_closedSpan
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ℕ → X →L[ℝ] ℝ) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    {s : Set X}
    (hs : ∀ x ∈ s, Tendsto (fun n => φ n x) atTop (𝓝 0))
    {x : X} (hx : x ∈ (Submodule.span ℝ s).topologicalClosure) :
    Tendsto (fun n => φ n x) atTop (𝓝 0) := by
  have hspan : ∀ y ∈ Submodule.span ℝ s,
      Tendsto (fun n => φ n y) atTop (𝓝 0) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hs y hy
    | zero =>
        simpa only [map_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    | add y z _ _ hy hz =>
        simpa only [map_add, add_zero] using hy.add hz
    | smul a y _ hy =>
        simpa only [map_smul, smul_zero] using hy.const_smul a
  change x ∈ closure (Submodule.span ℝ s : Set X) at hx
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hspan y hy) (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hdist : dist (φ n x) (φ n y) ≤ dist x y := by
    calc
      dist (φ n x) (φ n y) ≤ ‖φ n‖ * dist x y := (φ n).dist_le_opNorm x y
      _ ≤ 1 * dist x y := mul_le_mul_of_nonneg_right (hφ n) dist_nonneg
      _ = dist x y := one_mul _
  calc
    dist (φ n x) 0 ≤ dist (φ n x) (φ n y) + dist (φ n y) 0 := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hdist.trans_lt hxy) (hN n hn)
    _ = ε := add_halves ε

end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints
open Filter Topology


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.tendsto_zero_of_mem_closedSpan := @_root_.OAI.ReflexiveFixedPoints.tendsto_zero_of_mem_closedSpan
