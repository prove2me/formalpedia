-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.OrderedTree.lt_descendantHi_iff_ancestorLE_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:44:40.211732+00:00
-- url     : https://prove2.me/submissions/27ec015e-2adf-4737-b2fb-726b7562fa3a

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
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.OrderedTree
open scoped BigOperators

theorem rfp_anc_mono (T : OrderedTree) {i j : ℕ} (h : i ≤ j) : Monotone (T.ancestorLE h) := by
  induction h using Nat.leRec with
  | refl => simpa using monotone_id
  | @le_succ_of_le j h ih =>
      rw [T.ancestorLE_step h]
      exact ih.comp (T.parent_monotone j)

theorem rfp_lt_lo (T : OrderedTree) {i j : ℕ} (h : i ≤ j) (v : T.Node i) (s : T.Node j) :
    s.val < T.descendantLo h v ↔ T.ancestorLE h s < v := by
  have hf := T.ancestorLE_descendantFirst h v
  constructor
  · intro hs
    by_contra hc
    push Not at hc
    rcases hc.lt_or_eq with hlt | heq
    · have := rfp_anc_mono T h (le_of_lt (show s < T.descendantFirst h v from hs))
      rw [hf] at this
      exact absurd hlt (not_lt.mpr this)
    · have hmem : s ∈ T.descendants h v := (T.mem_descendants h v s).2 heq.symm
      have := Finset.min'_le _ _ hmem
      exact absurd hs (not_lt.mpr this)
  · intro hs
    by_contra hc
    push Not at hc
    have := rfp_anc_mono T h (show T.descendantFirst h v ≤ s from hc)
    rw [hf] at this
    exact absurd hs (not_lt.mpr this)

theorem rfp_lt_hi (T : OrderedTree) {i j : ℕ} (h : i ≤ j) (v : T.Node i) (s : T.Node j) :
    s.val < T.descendantHi h v ↔ T.ancestorLE h s ≤ v := by
  have hl := T.ancestorLE_descendantLast h v
  have e : s.val < T.descendantHi h v ↔ s ≤ T.descendantLast h v := by
    simp only [descendantHi, Nat.lt_succ_iff]; exact Iff.rfl
  rw [e]
  constructor
  · intro hs
    have := rfp_anc_mono T h hs
    rwa [hl] at this
  · intro hs
    by_contra hc
    push Not at hc
    have := rfp_anc_mono T h hc.le
    rw [hl] at this
    have heq : T.ancestorLE h s = v := le_antisymm hs this
    have hmem : s ∈ T.descendants h v := (T.mem_descendants h v s).2 heq
    exact absurd (Finset.le_max' _ _ hmem) (not_le.mpr hc)


variable (T : OrderedTree) {i j : ℕ}
theorem solution (h : i ≤ j)
    (v : T.Node i) (s : T.Node j) :
    s.val < T.descendantHi h v ↔ T.ancestorLE h s ≤ v :=
  rfp_lt_hi T h v s
