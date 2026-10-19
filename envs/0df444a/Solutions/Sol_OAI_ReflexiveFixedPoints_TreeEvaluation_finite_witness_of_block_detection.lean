-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.TreeEvaluation.finite_witness_of_block_detection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:42:37.601933+00:00
-- url     : https://prove2.me/submissions/f5e1dd12-369d-4748-8fa0-102f3bc93b66

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

open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open Filter Topology
open scoped BigOperators

theorem rfp_fwd
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

theorem rfp_telescope {k N : ℕ} (h : k ≤ N)
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

theorem rfp_pw_nonneg (W : WeightedTree T) (k : ℕ) (v : T.Node k) : 0 ≤ W.pathWeight k v := by
  induction k with
  | zero => simp
  | succ k ih => rw [WeightedTree.pathWeight_succ]; exact mul_nonneg (ih _) (W.weight_nonneg k v)

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

theorem rfp_eval_le (k : ℕ) : ∀ (H H' : T.Node k → K),
    ‖(E.evaluate k H : X) - E.evaluate k H'‖ ≤
      ∑ v, W.pathWeight k v * ‖(H v : X) - H' v‖ := by
  induction k with
  | zero =>
    intro H H'
    simp only [evaluate_zero, WeightedTree.pathWeight_zero, one_mul]
    exact Finset.single_le_sum (f := fun v => ‖(H v : X) - H' v‖)
      (fun v _ => norm_nonneg _) (Finset.mem_univ _)
  | succ k ih =>
    intro H H'
    rw [evaluate_succ, evaluate_succ]
    refine (ih _ _).trans ?_
    calc ∑ p, W.pathWeight k p * ‖(E.collapse k H p : X) - E.collapse k H' p‖
        ≤ ∑ p, W.pathWeight k p * ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
            W.weight k c * ‖(H c : X) - H' c‖ := by
          refine Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left ?_ ?_)
          · exact (rfp_map_le E k p _ _).trans (rfp_avg_le E k H H' p)
          · exact rfp_pw_nonneg W k p
      _ = ∑ c, W.pathWeight (k + 1) c * ‖(H c : X) - H' c‖ := by
          rw [← Finset.sum_fiberwise Finset.univ (T.parent k)
            (fun c => W.pathWeight (k + 1) c * ‖(H c : X) - H' c‖)]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun c hc => ?_)
          rw [WeightedTree.pathWeight_succ, (Finset.mem_filter.mp hc).2]; ring

theorem rfp_sum_desc_children {k n : ℕ} (h : k ≤ n)
    (v : T.Node k) (f : T.Node (n + 1) → ℝ) :
    (∑ p ∈ T.descendants h v, W.pathWeight n p *
      (∑ c ∈ Finset.univ.filter (fun c => T.parent n c = p), W.weight n c * f c)) =
      ∑ c ∈ T.descendants (Nat.le_succ_of_le h) v, W.pathWeight (n + 1) c * f c := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := T.descendants (Nat.le_succ_of_le h) v)
    (t := T.descendants h v) (g := T.parent n)]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mul_sum]
    have hs : (T.descendants (Nat.le_succ_of_le h) v).filter (fun c => T.parent n c = p) =
        Finset.univ.filter (fun c => T.parent n c = p) := by
      ext c
      simp only [Finset.mem_filter, OrderedTree.mem_descendants, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hc
        refine ⟨?_, hc⟩
        rw [T.ancestorLE_step h]
        simp only [Function.comp_apply, hc]
        exact (OrderedTree.mem_descendants _ _ _ _).1 hp
    rw [hs]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [WeightedTree.pathWeight_succ, (Finset.mem_filter.mp hc).2]; ring
  · intro c hc
    rw [OrderedTree.mem_descendants] at hc ⊢
    rw [T.ancestorLE_step h] at hc
    exact hc

theorem rfp_desc_weight {k N : ℕ} (h : k ≤ N) (v : T.Node k) :
    ∑ s ∈ T.descendants h v, W.pathWeight N s = W.pathWeight k v := by
  induction h using Nat.leRec with
  | refl =>
    rw [Finset.sum_eq_single v]
    · intro b hb hbv; simp at hb; exact absurd hb hbv
    · intro hv; simp at hv
  | @le_succ_of_le n h ih =>
    have := rfp_sum_desc_children (W := W) h v (fun _ => 1)
    simp only [mul_one, W.weight_sum] at this
    rw [← this, ih]

theorem rfp_level_weight (N : ℕ) : ∑ s : T.Node N, W.pathWeight N s = 1 := by
  have h := rfp_desc_weight (W := W) (Nat.zero_le N) T.root
  rw [WeightedTree.pathWeight_zero] at h
  rw [← h]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext s
  simp only [Finset.mem_univ, OrderedTree.mem_descendants, true_iff]
  apply Fin.ext
  have h1 := (T.ancestorLE (Nat.zero_le N) s).isLt
  have h2 := (T.root).isLt
  have h0 := T.size_zero
  omega

theorem rfp_switch_le (N : ℕ) (y : T.Node N → K) (b : K) (s : T.Node N) :
    ‖(E.switchRoot N y b (s.val + 1) : X) - E.switchRoot N y b s.val‖ ≤
      W.pathWeight N s * ‖(y s : X) - b‖ := by
  unfold switchRoot
  refine (rfp_eval_le E N _ _).trans (le_of_eq ?_)
  rw [Finset.sum_eq_single s]
  · simp [switchLeaves]
  · intro u _ hu
    have hne : u.val ≠ s.val := fun h => hu (Fin.ext h)
    have hiff : (u.val < s.val + 1 ↔ u.val < s.val) := by omega
    simp only [switchLeaves, hiff, sub_self, norm_zero, mul_zero]
  · simp

theorem solution
    (N : ℕ) (y : T.Node N → K) (b : K)
    (Y : Submodule ℝ X) (hY : ∀ a c : K, (a : X) - c ∈ Y)
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1)
    (f : (k : ℕ) → T.Node k → X →L[ℝ] ℝ)
    (hf : ∀ k v, ‖f k v‖ ≤ 1)
    (e : T.TruncationNode N → ℝ)
    (he : (∑ v, e v) ≤ (1 : ℝ) / 128)
    (hblock : ∀ v : T.TruncationNode N,
      W.pathWeight (v.1.val + 1) v.2 - 5 * e v ≤
        f (v.1.val + 1) v.2
          ((E.beforeBlock v.levelBound y b v.2 : X) -
            E.afterBlock v.levelBound y b v.2)) :
    ∃ s : T.Node N,
      E.switchVector N y b s ∈ Y ∧ ‖E.switchVector N y b s‖ ≤ 1 ∧
        ∀ i (hi : i ≤ N), 0 < i →
          (1 : ℝ) / 2 ≤ f i (T.ancestorLE hi s) (E.switchVector N y b s) := by
  classical
  have hsv_norm : ∀ s, ‖E.switchVector N y b s‖ ≤ 1 := by
    intro s
    have hp := rfp_pw_pos W N s
    simp only [switchVector, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp]
    rw [inv_mul_le_iff₀ hp, mul_one]
    have := hdiam (y s) b
    exact (rfp_switch_le E N y b s).trans (by nlinarith)
  have hsv_mem : ∀ s, E.switchVector N y b s ∈ Y := fun s => Y.smul_mem _ (hY _ _)
  let R : T.TruncationNode N → T.Node N → Prop := fun v s => T.ancestorLE v.levelBound s = v.2
  let a : T.TruncationNode N → T.Node N → ℝ := fun v s => f (v.1.val + 1) v.2 (E.switchVector N y b s)
  have ha : ∀ v s, R v s → a v s ≤ 1 := by
    intro v s _
    have h1 := (f (v.1.val + 1) v.2).le_opNorm (E.switchVector N y b s)
    have h2 := Real.le_norm_self (a v s)
    have h3 := hf (v.1.val + 1) v.2
    have h4 := hsv_norm s
    have h5 := norm_nonneg (f (v.1.val + 1) v.2)
    have h6 := norm_nonneg (E.switchVector N y b s)
    simp only [a] at h2 ⊢
    nlinarith
  have hrow : ∀ v, (∑ s, if R v s then W.pathWeight N s * (1 - a v s) else 0) ≤ 5 * e v := by
    intro v
    rw [← Finset.sum_filter]
    have hfil : Finset.univ.filter (fun s => R v s) = T.descendants v.levelBound v.2 := by
      ext s; simp [R]
    rw [hfil]
    have hsum : ∑ s ∈ T.descendants v.levelBound v.2, W.pathWeight N s * a v s =
        f (v.1.val + 1) v.2 ((E.beforeBlock v.levelBound y b v.2 : X) - E.afterBlock v.levelBound y b v.2) := by
      rw [← rfp_telescope E v.levelBound y b v.2, map_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [map_smul, smul_eq_mul]
    have := hblock v
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, rfp_desc_weight]
    linarith
  obtain ⟨-, -, s, -, hs⟩ := rfp_fwd R (W.pathWeight N) e a (fun s => (rfp_pw_pos W N s).le)
    (rfp_level_weight N) ha hrow he
  refine ⟨s, hsv_mem s, hsv_norm s, ?_⟩
  intro i hi hi0
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  exact (hs ⟨⟨j, by omega⟩, T.ancestorLE hi s⟩ rfl).le
