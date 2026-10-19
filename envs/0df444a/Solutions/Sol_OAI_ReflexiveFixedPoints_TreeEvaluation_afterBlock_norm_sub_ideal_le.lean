-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.TreeEvaluation.afterBlock_norm_sub_ideal_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:40:36.324093+00:00
-- url     : https://prove2.me/submissions/42a6fbe9-7479-4651-a7b5-710fc5c75565

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

open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.OrderedTree OAI.ReflexiveFixedPoints.TreeEvaluation
open Filter Topology
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


variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

theorem rfp_avg_le (k : ℕ) (H H' : T.Node (k + 1) → K)
    (p : T.Node k) :
    ‖(E.childAverage k H p : X) - E.childAverage k H' p‖ ≤
      ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - H' c‖ := by
  rw [childAverage_val, childAverage_val, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun c _ => ?_)))
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (W.weight_pos k c)]

theorem rfp_map_le (k : ℕ) (v : T.Node k) (a b : K) :
    ‖(E.map k v a : X) - E.map k v b‖ ≤ ‖(a : X) - b‖ := by
  have := (E.nonexpansive k v).dist_le_mul a b
  simpa [Subtype.dist_eq, dist_eq_norm] using this


theorem rfp_sub_sup {i j : ℕ} (h : i ≤ j) :
    ∀ (H H' : T.Node j → K) (v : T.Node i) (c : ℝ),
      (∀ s, T.ancestorLE h s = v → ‖(H s : X) - H' s‖ ≤ c) →
      ‖(E.subtreeOutput h H v : X) - E.subtreeOutput h H' v‖ ≤ c := by
  induction h using Nat.leRec with
  | refl =>
    intro H H' v c hc
    simp only [subtreeOutput_refl_apply]
    exact hc v (by simp)
  | @le_succ_of_le j h ih =>
    intro H H' v c hc
    rw [E.subtreeOutput_step h, E.subtreeOutput_step h]
    apply ih
    intro p hp
    simp only [collapse]
    refine (rfp_map_le E j p _ _).trans ((rfp_avg_le E j H H' p).trans ?_)
    calc (∑ c' ∈ Finset.univ.filter (fun c' => T.parent j c' = p), W.weight j c' * ‖(H c' : X) - H' c'‖)
        ≤ ∑ c' ∈ Finset.univ.filter (fun c' => T.parent j c' = p), W.weight j c' * c := by
          refine Finset.sum_le_sum (fun c' hc' => mul_le_mul_of_nonneg_left (hc c' ?_) (W.weight_nonneg j c'))
          rw [T.ancestorLE_step h]
          simp [(Finset.mem_filter.mp hc').2, hp]
      _ = c := by rw [← Finset.sum_mul, W.weight_sum, one_mul]

theorem rfp_sub_map (x : K) (τ : ℕ → ℝ) {k N : ℕ} (h : k ≤ N)
    (havg : ∀ d, d < N → ∀ p : T.Node d,
      ‖(E.childAverage d (fun c => E.map (d + 1) c x) p : X) - x‖ ≤ τ d) (u : T.Node k) :
    ‖(E.subtreeOutput h (fun s => E.map N s x) u : X) - E.map k u x‖ ≤ ∑ d ∈ Finset.Ico k N, τ d := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le N h ih =>
    rw [E.subtreeOutput_step h, Finset.sum_Ico_succ_top h]
    have ih' := ih (fun d hd p => havg d (Nat.lt_succ_of_lt hd) p)
    have h1 : ‖(E.subtreeOutput h (E.collapse N (fun s => E.map (N + 1) s x)) u : X) -
        E.subtreeOutput h (fun s => E.map N s x) u‖ ≤ τ N := by
      apply rfp_sub_sup E h _ _ u
      intro p _
      simp only [collapse]
      exact (rfp_map_le E N p _ _).trans (havg N (Nat.lt_succ_self N) p)
    calc _ ≤ ‖(E.subtreeOutput h (E.collapse N (fun s => E.map (N + 1) s x)) u : X) -
        E.subtreeOutput h (fun s => E.map N s x) u‖ +
          ‖(E.subtreeOutput h (fun s => E.map N s x) u : X) - E.map k u x‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by linarith

theorem rfp_sub_const (b : K) {k N : ℕ} (h : k ≤ N) (u : T.Node k) :
    ‖(E.subtreeOutput h (fun _ => b) u : X) - b‖ ≤
      ∑ d ∈ Finset.Ico k N, ∑ p : T.Node d, ‖(E.map d p b : X) - b‖ := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le N h ih =>
    rw [E.subtreeOutput_step h, Finset.sum_Ico_succ_top h]
    have hcol : E.collapse N (fun _ => b) = fun p => E.map N p b := by
      funext p; simp only [collapse, childAverage_const]
    rw [hcol]
    have h1 : ‖(E.subtreeOutput h (fun p => E.map N p b) u : X) -
        E.subtreeOutput h (fun _ => b) u‖ ≤ ∑ p : T.Node N, ‖(E.map N p b : X) - b‖ := by
      apply rfp_sub_sup E h _ _ u
      intro p _
      exact Finset.single_le_sum (f := fun p => ‖(E.map N p b : X) - b‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ p)
    calc _ ≤ ‖(E.subtreeOutput h (fun p => E.map N p b) u : X) -
        E.subtreeOutput h (fun _ => b) u‖ + ‖(E.subtreeOutput h (fun _ => b) u : X) - b‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by linarith

theorem rfp_sub_congr' {i j : ℕ} (h : i ≤ j) :
    ∀ (H H' : T.Node j → K) (v : T.Node i),
      (∀ s, T.ancestorLE h s = v → H s = H' s) →
      E.subtreeOutput h H v = E.subtreeOutput h H' v := by
  induction h using Nat.leRec with
  | refl =>
    intro H H' v hv
    simp only [subtreeOutput_refl_apply]
    exact hv v (by simp)
  | @le_succ_of_le j h ih =>
    intro H H' v hv
    rw [E.subtreeOutput_step h, E.subtreeOutput_step h]
    apply ih
    intro s hs
    simp only [collapse]
    congr 1
    apply Subtype.ext
    simp only [childAverage_val]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [hv c (by rw [T.ancestorLE_step h]; simp [(Finset.mem_filter.mp hc).2, hs])]

theorem solution
    (x b : K) (τ : ℕ → ℝ) {k N : ℕ} (h : k ≤ N) (v : T.Node k)
    (haverage : ∀ d, d < N → ∀ p : T.Node d,
      ‖(E.childAverage d (fun c => E.map (d + 1) c x) p : X) - x‖ ≤ τ d)
    {e : ℝ} (htail : (∑ d ∈ Finset.Ico k N, τ d) ≤ e)
    (hterminal : E.terminalDefect N b ≤ e) :
    ‖(E.afterBlock h (fun s => E.map N s x) b v : X) -
      E.evaluate k (E.idealCutoff k x b v)‖ ≤ e := by
  classical
  have hL : ∀ u : T.Node k, ‖(E.subtreeOutput h
      (E.switchLeaves N (fun s => E.map N s x) b (T.descendantLo h v)) u : X) -
      E.idealCutoff k x b v u‖ ≤ e := by
    intro u
    by_cases hu : u < v
    · rw [rfp_sub_congr' E h _ (fun s => E.map N s x) u (fun s hs => by
          simp only [switchLeaves]; rw [if_pos ((rfp_lt_lo T h v s).2 (hs ▸ hu))])]
      simp only [idealCutoff, if_pos hu]
      exact (rfp_sub_map E x τ h haverage u).trans htail
    · rw [rfp_sub_congr' E h _ (fun _ => b) u (fun s hs => by
          simp only [switchLeaves]; rw [if_neg (fun h' => hu (hs ▸ (rfp_lt_lo T h v s).1 h'))])]
      simp only [idealCutoff, if_neg hu]
      refine (rfp_sub_const E b h u).trans (le_trans ?_ hterminal)
      unfold terminalDefect
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      intro d hd; simp only [Finset.mem_Ico, Finset.mem_range] at hd ⊢; omega
  unfold afterBlock switchRoot
  rw [E.evaluate_subtreeOutput h, ← E.subtreeOutput_zero_root k, ← E.subtreeOutput_zero_root k]
  exact rfp_sub_sup E (Nat.zero_le k) _ _ T.root e (fun u _ => hL u)
