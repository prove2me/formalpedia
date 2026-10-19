-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.finite_weighted_deficit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:37:05.685955+00:00
-- url     : https://prove2.me/submissions/b59eca3f-2959-4eeb-ab85-79fb0b9f0259

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

open OAI OAI.ReflexiveFixedPoints
open scoped BigOperators
theorem solution
    {V S : Type*} [Fintype V] [Fintype S]
    (R : V → S → Prop) [DecidableRel R]
    (w : S → ℝ) (e : V → ℝ) (a : V → S → ℝ)
    (hw : ∀ s, 0 ≤ w s)
    (hw_sum : (∑ s, w s) = 1)
    (ha : ∀ v s, R v s → a v s ≤ 1)
    (hrow : ∀ v,
      (∑ s, if R v s then w s * (1 - a v s) else 0) ≤ 5 * e v)
    (he_sum : (∑ v, e v) ≤ (1 : ℝ) / 128) :
    (∑ s, w s * pathDeficit R a s) ≤ (5 : ℝ) / 128 ∧
      badLeafMass R w a ≤ (5 : ℝ) / 64 ∧
      ∃ s, 0 < w s ∧ ∀ v, R v s → (1 : ℝ) / 2 < a v s := by
  classical
  have hterm : ∀ v s, 0 ≤ (if R v s then 1 - a v s else 0) := by
    intro v s; split_ifs with h
    · linarith [ha v s h]
    · exact le_refl 0
  have hpd : ∀ s, 0 ≤ pathDeficit R a s := fun s => Finset.sum_nonneg (fun v _ => hterm v s)
  have h1 : (∑ s, w s * pathDeficit R a s) ≤ (5 : ℝ) / 128 := by
    have : (∑ s, w s * pathDeficit R a s) = ∑ v, ∑ s, (if R v s then w s * (1 - a v s) else 0) := by
      unfold pathDeficit
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun s _ => ?_))
      split_ifs <;> simp
    rw [this]
    calc (∑ v, ∑ s, (if R v s then w s * (1 - a v s) else 0)) ≤ ∑ v, 5 * e v :=
          Finset.sum_le_sum (fun v _ => hrow v)
      _ = 5 * ∑ v, e v := by rw [Finset.mul_sum]
      _ ≤ 5 * (1 / 128) := by linarith
      _ = 5 / 128 := by norm_num
  have hbad : ∀ s, IsBadLeaf R a s → (1 : ℝ) / 2 ≤ pathDeficit R a s := by
    rintro s ⟨v, hv, hav⟩
    unfold pathDeficit
    calc (1 : ℝ) / 2 ≤ (if R v s then 1 - a v s else 0) := by rw [if_pos hv]; linarith
      _ ≤ ∑ v, (if R v s then 1 - a v s else 0) :=
          Finset.single_le_sum (f := fun v => if R v s then 1 - a v s else 0)
            (fun v _ => hterm v s) (Finset.mem_univ v)
  have h2 : badLeafMass R w a ≤ (5 : ℝ) / 64 := by
    unfold badLeafMass
    calc (∑ s, if IsBadLeaf R a s then w s else 0) ≤ ∑ s, 2 * (w s * pathDeficit R a s) := by
          refine Finset.sum_le_sum (fun s _ => ?_)
          split_ifs with h
          · have := hbad s h
            nlinarith [hw s]
          · have := hpd s; have := hw s; positivity
      _ = 2 * ∑ s, w s * pathDeficit R a s := by rw [Finset.mul_sum]
      _ ≤ 2 * (5 / 128) := by linarith
      _ = 5 / 64 := by norm_num
  refine ⟨h1, h2, ?_⟩
  by_contra hcon
  push_neg at hcon
  have : (1 : ℝ) ≤ badLeafMass R w a := by
    unfold badLeafMass
    rw [← hw_sum]
    refine Finset.sum_le_sum (fun s _ => ?_)
    rcases (hw s).lt_or_eq with hpos | hzero
    · obtain ⟨v, hv, hav⟩ := hcon s hpos
      rw [if_pos ⟨v, hv, hav⟩]
    · rw [← hzero]; split_ifs <;> simp
  linarith
