-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.OrderedTree.exists_feasible_branch
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:37:12.73899+00:00
-- url     : https://prove2.me/submissions/c52cd711-d6ab-47c8-aa04-51984ff2a05e

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

open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.OrderedTree
theorem rfp_anc_trans (T : OrderedTree) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (s : T.Node k) :
    T.ancestorLE hij (T.ancestorLE hjk s) = T.ancestorLE (hij.trans hjk) s := by
  induction hjk using Nat.leRec with
  | refl => simp
  | @le_succ_of_le k hjk ih =>
      have h1 := congrFun (T.ancestorLE_step hjk) s
      have h2 := congrFun (T.ancestorLE_step (hij.trans hjk)) s
      simp only [Function.comp] at h1 h2
      rw [h1, ih, ← h2]

theorem rfp_feasible_anc (T : OrderedTree) {D : Type*} (B : Set D) (f : (k : ℕ) → T.Node k → D → ℝ)
    {m n : ℕ} (h : m ≤ n) (s : T.Node n) (hs : T.Feasible B f s) :
    T.Feasible B f (T.ancestorLE h s) := by
  obtain ⟨d, hd, hdet⟩ := hs
  refine ⟨d, hd, fun i hi hi0 => ?_⟩
  rw [rfp_anc_trans]
  exact hdet i (hi.trans h) hi0

variable (T : OrderedTree) {D : Type*}
variable (B : Set D) (f : (k : ℕ) → T.Node k → D → ℝ)
theorem solution
    (hne : ∀ n, ∃ v : T.Node n, T.Feasible B f v) :
    ∃ b : (n : ℕ) → T.Node n,
      T.IsBranch b ∧ ∀ n, T.Feasible B f (b n) := by
  classical
  -- a node is good if it has feasible descendants at every later level
  let Good : (n : ℕ) → T.Node n → Prop := fun n v =>
    ∀ m (h : n ≤ m), ∃ s : T.Node m, T.Feasible B f s ∧ T.ancestorLE h s = v
  have hroot : Good 0 (T.root) := by
    intro m h
    obtain ⟨s, hs⟩ := hne m
    refine ⟨s, hs, ?_⟩
    apply Fin.ext
    have h1 := (T.ancestorLE h s).isLt
    have h2 := (T.root).isLt
    have h0 := T.size_zero
    omega
  have hchild : ∀ n (v : T.Node n), Good n v → ∃ c : T.Node (n + 1), T.parent n c = v ∧ Good (n + 1) c := by
    intro n v hv
    by_contra hcon
    push_neg at hcon
    have hbad : ∀ c : T.Node (n + 1), ∃ m, ∃ h : n + 1 ≤ m,
        ∀ s : T.Node m, T.Feasible B f s → T.parent n c = v → T.ancestorLE h s ≠ c := by
      intro c
      by_cases hc : T.parent n c = v
      · have := hcon c hc
        simp only [Good, not_forall, not_exists, not_and] at this
        obtain ⟨m, h, hm⟩ := this
        exact ⟨m, h, fun s hs _ => hm s hs⟩
      · exact ⟨n + 1, le_refl _, fun s _ hc' => absurd hc' hc⟩
    choose mc hmc hmc' using hbad
    let M := n + 1 + ∑ c, mc c
    have hMc : ∀ c, mc c ≤ M := fun c => by
      have := Finset.single_le_sum (f := mc) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
    have hnM : n ≤ M := by omega
    have hn1M : n + 1 ≤ M := by omega
    obtain ⟨s, hs, hsv⟩ := hv M hnM
    let c := T.ancestorLE hn1M s
    have hpc : T.parent n c = v := by
      have : T.parent n c = T.ancestorLE (Nat.le_succ n) c := by simp
      rw [this, rfp_anc_trans]; exact hsv
    apply hmc' c (T.ancestorLE (hMc c) s) (rfp_feasible_anc T B f _ s hs) hpc
    rw [rfp_anc_trans]
  choose next hnext_par hnext_good using hchild
  let b' : (n : ℕ) → {v : T.Node n // Good n v} := fun n =>
    Nat.rec ⟨T.root, hroot⟩ (fun n p => ⟨next n p.1 p.2, hnext_good n p.1 p.2⟩) n
  have hb'succ : ∀ n, (b' (n + 1)).1 = next n (b' n).1 (b' n).2 := fun n => rfl
  refine ⟨fun n => (b' n).1, ?_, ?_⟩
  · intro i j hij
    induction hij using Nat.leRec with
    | refl => simp
    | @le_succ_of_le j h ih =>
        have h1 := congrFun (T.ancestorLE_step h) (b' (j + 1)).1
        simp only [Function.comp] at h1
        rw [h1, hb'succ, hnext_par]
        exact ih
  · intro n
    obtain ⟨s, hs, hsv⟩ := (b' n).2 n (le_refl n)
    simp only [OrderedTree.ancestorLE_refl_apply] at hsv
    show T.Feasible B f (b' n).1
    rw [← hsv]; exact hs
