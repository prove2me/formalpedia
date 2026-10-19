-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.abs_apply_sub_le_of_detector
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T18:18:38.843779+00:00
-- url     : https://prove2.me/submissions/b33bb93b-4666-43b7-893c-e1241b066876

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/BranchContradiction.lean:L25-L41
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.abs_apply_sub_le_of_detector. The node keeps its source
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

/-- Two detector values in the same interval of length e differ by at most e. -/
theorem abs_apply_sub_le_of_detector (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1)
    (y a b : X) (e : ℝ)
    (hya : ‖y - a‖ ≤ 1) (hyb : ‖y - b‖ ≤ 1)
    (ha : 1 - e ≤ f (y - a)) (hb : 1 - e ≤ f (y - b)) :
    |f (a - b)| ≤ e := by
  have hupper (z : X) (hz : ‖y - z‖ ≤ 1) : f (y - z) ≤ 1 := by
    calc
      f (y - z) ≤ |f (y - z)| := le_abs_self _
      _ = ‖f (y - z)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ * ‖y - z‖ := f.le_opNorm _
      _ ≤ 1 * 1 := mul_le_mul hf hz (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  have hua := hupper a hya
  have hub := hupper b hyb
  simp only [map_sub] at ha hb hua hub ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints
open Filter Topology


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.abs_apply_sub_le_of_detector := @_root_.OAI.ReflexiveFixedPoints.abs_apply_sub_le_of_detector
