-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.tendsto_zero_of_mem_closedSpan
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:34:28.829236+00:00
-- url     : https://prove2.me/submissions/60090113-b0fb-49af-bfb5-5114c337a667

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

open OAI OAI.ReflexiveFixedPoints
open Filter Topology
theorem solution
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ℕ → X →L[ℝ] ℝ) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    {s : Set X}
    (hs : ∀ x ∈ s, Tendsto (fun n => φ n x) atTop (𝓝 0))
    {x : X} (hx : x ∈ (Submodule.span ℝ s).topologicalClosure) :
    Tendsto (fun n => φ n x) atTop (𝓝 0) := by
  have hspan : ∀ x ∈ Submodule.span ℝ s, Tendsto (fun n => φ n x) atTop (𝓝 0) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h => exact hs x h
    | zero => simp
    | add x y _ _ hx hy => simpa using hx.add hy
    | smul c x _ hx => simpa using hx.const_mul c
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hx' : x ∈ closure (Submodule.span ℝ s : Set X) := by
    rwa [← Submodule.topologicalClosure_coe]
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx' (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hspan z hz) (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  have h2 : |φ n x - φ n z| ≤ dist x z := by
    rw [← map_sub, ← Real.norm_eq_abs, dist_eq_norm]
    calc ‖φ n (x - z)‖ ≤ ‖φ n‖ * ‖x - z‖ := (φ n).le_opNorm _
      _ ≤ 1 * ‖x - z‖ := by gcongr; exact hφ n
      _ = ‖x - z‖ := one_mul _
  calc |φ n x| = |(φ n x - φ n z) + φ n z| := by ring_nf
    _ ≤ |φ n x - φ n z| + |φ n z| := abs_add_le _ _
    _ < ε := by linarith
