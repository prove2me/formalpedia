-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.TreeEvaluation.switchVector_block_telescope
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:52:19.309565+00:00
-- url     : https://prove2.me/submissions/075f2a07-ebd4-496c-aa80-9aac18be890a

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

open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)
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
    simp only [OrderedTree.descendantHi, Nat.lt_succ_iff]; exact Iff.rfl
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

theorem rfp_sum_Ico (T : OrderedTree)
    {k N : ℕ} (h : k ≤ N) (v : T.Node k)
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    (∑ s ∈ T.descendants h v, f s.val) =
      ∑ i ∈ Finset.Ico (T.descendantLo h v) (T.descendantHi h v), f i := by
  have hmap : (T.descendants h v).map Fin.valEmbedding =
      Finset.Ico (T.descendantLo h v) (T.descendantHi h v) := by
    ext n
    simp only [Finset.mem_map, Fin.valEmbedding_apply, Finset.mem_Ico, OrderedTree.mem_descendants]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have := (rfp_lt_hi T h v s).2 hs.le
      have h2 : ¬ s.val < T.descendantLo h v := fun hh => absurd hs (ne_of_lt ((rfp_lt_lo T h v s).1 hh))
      exact ⟨not_lt.mp h2, this⟩
    · rintro ⟨h1, h2⟩
      have hn : n < T.size N := by
        have := (T.descendantLast h v).isLt
        simp only [OrderedTree.descendantHi] at h2
        omega
      refine ⟨⟨n, hn⟩, ?_, rfl⟩
      have a := (rfp_lt_hi T h v ⟨n, hn⟩).1 h2
      have b : ¬ T.ancestorLE h ⟨n, hn⟩ < v := fun hh => absurd h1 (not_le.mpr ((rfp_lt_lo T h v _).2 hh))
      exact le_antisymm a (not_lt.mp b)
  rw [← hmap, Finset.sum_map]
  rfl

theorem rfp_pw_pos (W : WeightedTree T) (k : ℕ) (v : T.Node k) : 0 < W.pathWeight k v := by
  induction k with
  | zero => simp
  | succ k ih => rw [WeightedTree.pathWeight_succ]; exact mul_pos (ih _) (W.weight_pos k v)

theorem solution {k N : ℕ} (h : k ≤ N)
    (y : T.Node N → K) (b : K) (v : T.Node k) :
    (∑ s ∈ T.descendants h v, W.pathWeight N s • E.switchVector N y b s) =
      (E.beforeBlock h y b v : X) - E.afterBlock h y b v := by
  have : ∀ s ∈ T.descendants h v, W.pathWeight N s • E.switchVector N y b s =
      (fun i : ℕ => (E.switchRoot N y b (i + 1) : X) - E.switchRoot N y b i) s.val := by
    intro s _
    simp only [switchVector, smul_smul, mul_inv_cancel₀ (rfp_pw_pos W N s).ne', one_smul]
  rw [Finset.sum_congr rfl this, rfp_sum_Ico T h v (fun i : ℕ => (E.switchRoot N y b (i + 1) : X) - E.switchRoot N y b i)]
  rw [Finset.sum_Ico_sub (fun i : ℕ => (E.switchRoot N y b i : X))]
  · rfl
  · simp only [OrderedTree.descendantLo, OrderedTree.descendantHi, OrderedTree.descendantFirst,
      OrderedTree.descendantLast]
    have := Finset.min'_le_max' (T.descendants h v) (T.descendants_nonempty h v)
    have : ((T.descendants h v).min' _ : ℕ) ≤ ((T.descendants h v).max' _ : ℕ) := this
    omega
