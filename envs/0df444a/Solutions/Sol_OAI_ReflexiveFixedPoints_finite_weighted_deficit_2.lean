-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.finite_weighted_deficit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:59:16.298995+00:00
-- url     : https://prove2.me/submissions/b6b16961-b4b7-4795-8945-03e1f55d5866

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/WeightedDeficit.lean:L44-L132
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.finite_weighted_deficit. The node keeps its source
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

-- ---- from OAI.Analysis.Nonexpansive.WeightedDeficit ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
Finite weighted deficits used after the actual leaf-switching estimates.

The scalar argument allows zero leaf weights and returns a positive-weight leaf.
The application constructs its vectors using the strictly positive path weights,
then supplies the row estimates through `block_deficit_of_detection`.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

/-- Finite double counting gives a common leaf without a lower bound on weights.

The first two conclusions retain the quantitative estimates. The
selected leaf has positive weight and satisfies every incident detector strictly.
-/
theorem finite_weighted_deficit
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
  have hterm (v : V) (s : S) :
      0 ≤ (if R v s then 1 - a v s else 0) := by
    by_cases h : R v s
    · simpa only [ite_eq_left h] using sub_nonneg.mpr (ha v s h)
    · simp only [ite_eq_right h, le_refl]
  have hpath (s : S) : 0 ≤ pathDeficit R a s := by
    exact Finset.sum_nonneg fun v _ => hterm v s
  have hexchange :
      (∑ s, w s * pathDeficit R a s) =
        ∑ v, ∑ s, if R v s then w s * (1 - a v s) else 0 := by
    simp only [pathDeficit, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : R v s <;> simp only [h, ite_true, ite_false, mul_zero]
  have htotal :
      (∑ s, w s * pathDeficit R a s) ≤ (5 : ℝ) / 128 := by
    calc
      (∑ s, w s * pathDeficit R a s) =
          ∑ v, ∑ s, if R v s then w s * (1 - a v s) else 0 := hexchange
      _ ≤ ∑ v, 5 * e v := Finset.sum_le_sum fun v _ => hrow v
      _ = 5 * ∑ v, e v := (Finset.mul_sum _ _ _).symm
      _ ≤ (5 : ℝ) / 128 := by linarith
  have hbad_path (s : S) (hs : IsBadLeaf R a s) :
      (1 : ℝ) / 2 ≤ pathDeficit R a s := by
    obtain ⟨v, hv, hva⟩ := hs
    have hsingle := Finset.single_le_sum
      (fun u (_ : u ∈ (Finset.univ : Finset V)) => hterm u s)
      (Finset.mem_univ v)
    change (if R v s then 1 - a v s else 0) ≤ pathDeficit R a s at hsingle
    rw [ite_eq_left hv] at hsingle
    linarith
  have hbad_half :
      badLeafMass R w a / 2 ≤ ∑ s, w s * pathDeficit R a s := by
    unfold badLeafMass
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro s _
    by_cases hs : IsBadLeaf R a s
    · rw [ite_eq_left hs]
      have hmul := mul_le_mul_of_nonneg_left (hbad_path s hs) (hw s)
      simpa only [div_eq_mul_inv, one_mul] using hmul
    · rw [ite_eq_right hs, zero_div]
      exact mul_nonneg (hw s) (hpath s)
  have hbad_mass : badLeafMass R w a ≤ (5 : ℝ) / 64 := by
    linarith
  refine ⟨htotal, hbad_mass, ?_⟩
  by_contra hnone
  have hbad_of_pos (s : S) (hs : 0 < w s) : IsBadLeaf R a s := by
    by_contra hgood
    apply hnone
    refine ⟨s, hs, ?_⟩
    intro v hv
    apply lt_of_not_ge
    intro hle
    exact hgood ⟨v, hv, hle⟩
  have hmass_one : badLeafMass R w a = 1 := by
    calc
      badLeafMass R w a = ∑ s, w s := by
        unfold badLeafMass
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : 0 < w s
        · exact ite_eq_left (hbad_of_pos s hs)
        · have hz : w s = 0 := le_antisymm (le_of_not_gt hs) (hw s)
          simp only [hz, ite_self]
      _ = 1 := hw_sum
  linarith

end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.finite_weighted_deficit := @_root_.OAI.ReflexiveFixedPoints.finite_weighted_deficit
