-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.SwitchingTreeData.finite_block_detection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:46:40.278733+00:00
-- url     : https://prove2.me/submissions/d73ebff5-2045-486e-be78-797165ecca59

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

section
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

theorem rfp_after
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

theorem rfp_pw_nonneg (W : WeightedTree T) (k : ℕ) (v : T.Node k) : 0 ≤ W.pathWeight k v := by
  induction k with
  | zero => simp
  | succ k ih => rw [WeightedTree.pathWeight_succ]; exact mul_nonneg (ih _) (W.weight_nonneg k v)

theorem rfp_weight_le_one (W : WeightedTree T) (k : ℕ) (c : T.Node (k + 1)) : W.weight k c ≤ 1 := by
  have h := W.weight_sum k (T.parent k c)
  rw [← h]
  exact Finset.single_le_sum (f := fun c => W.weight k c) (fun c _ => W.weight_nonneg k c)
    (by simp)

theorem rfp_pw_anc {i j : ℕ} (h : i ≤ j) (W : WeightedTree T) :
    ∀ s : T.Node j, W.pathWeight j s ≤ W.pathWeight i (T.ancestorLE h s) := by
  induction h using Nat.leRec with
  | refl => intro s; simp
  | @le_succ_of_le j h ih =>
    intro s
    rw [T.ancestorLE_step h, WeightedTree.pathWeight_succ, Function.comp_apply]
    calc W.pathWeight j (T.parent j s) * W.weight j s ≤ W.pathWeight j (T.parent j s) * 1 :=
          mul_le_mul_of_nonneg_left (rfp_weight_le_one W j s) (rfp_pw_nonneg W j _)
      _ ≤ _ := by rw [mul_one]; exact ih _

theorem rfp_pw_le_one (W : WeightedTree T) (k : ℕ) (v : T.Node k) : W.pathWeight k v ≤ 1 := by
  have := rfp_pw_anc (Nat.zero_le k) W v
  simpa using this

theorem rfp_focus
    (hdiam : ∀ a b : K, ‖(a : X) - b‖ ≤ 1)
    (k : ℕ) : ∀ (H : T.Node k → K) (v : T.Node k) (z : K),
    ‖(E.evaluate k H : X) - z‖ ≤
      W.pathWeight k v * ‖(H v : X) - z‖ + (1 - W.pathWeight k v) +
        E.weightedPathDisplacement k v z := by
  induction k with
  | zero =>
    intro H v z
    have hv : v = T.root := by
      apply Fin.ext
      have h1 : (v : ℕ) < T.size 0 := v.isLt
      have h2 := T.size_zero
      simp [OrderedTree.root]; omega
    subst hv
    simp
  | succ k ih =>
    intro H v z
    set p := T.parent k v
    rw [evaluate_succ]
    refine (ih _ p z).trans ?_
    have hδ : ‖(E.collapse k H p : X) - z‖ ≤
        (W.weight k v * ‖(H v : X) - z‖ + (1 - W.weight k v)) + ‖(E.map k p z : X) - z‖ := by
      have h1 : ‖(E.collapse k H p : X) - z‖ ≤
          ‖(E.childAverage k H p : X) - z‖ + ‖(E.map k p z : X) - z‖ := by
        calc ‖(E.collapse k H p : X) - z‖
            ≤ ‖(E.collapse k H p : X) - E.map k p z‖ + ‖(E.map k p z : X) - z‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ _ := add_le_add_left (rfp_map_le E k p _ _) _
      refine h1.trans (add_le_add_left ?_ _)
      have h2 := rfp_avg_le E k H (fun _ => z) p
      rw [childAverage_const] at h2
      refine h2.trans ?_
      have hv : v ∈ Finset.univ.filter (fun c => T.parent k c = p) := by simp [p]
      rw [← Finset.add_sum_erase _ _ hv]
      have hsum := W.weight_sum k p
      rw [← Finset.add_sum_erase _ _ hv] at hsum
      have : ∑ c ∈ (Finset.univ.filter (fun c => T.parent k c = p)).erase v,
          W.weight k c * ‖(H c : X) - z‖ ≤
          ∑ c ∈ (Finset.univ.filter (fun c => T.parent k c = p)).erase v, W.weight k c :=
        Finset.sum_le_sum (fun c _ => by
          have := hdiam (H c) z
          nlinarith [W.weight_nonneg k c])
      linarith
    have hp := rfp_pw_nonneg W k p
    rw [WeightedTree.pathWeight_succ, weightedPathDisplacement_succ]
    have := mul_le_mul_of_nonneg_left hδ hp
    nlinarith

theorem rfp_wpd_le (k : ℕ) : ∀ (v : T.Node k) (z : K),
    E.weightedPathDisplacement k v z ≤ E.pathDisplacement k v z := by
  induction k with
  | zero => intro v z; simp
  | succ k ih =>
    intro v z
    rw [weightedPathDisplacement_succ, pathDisplacement_succ]
    have h1 := ih (T.parent k v) z
    have h2 := rfp_pw_le_one W k (T.parent k v)
    have h3 := norm_nonneg ((E.map k (T.parent k v) z : X) - z)
    nlinarith

theorem rfp_before
    (hdiam : ∀ a b : K, ‖(a : X) - b‖ ≤ 1)
    (k : ℕ) (H : T.Node k → K) (v : T.Node k) (z : K) {e : ℝ}
    (hfocused : ‖(H v : X) - z‖ ≤ e)
    (hpath : E.pathDisplacement k v z ≤ e) :
    ‖(E.evaluate k H : X) - z‖ ≤ 1 - W.pathWeight k v + 2 * e := by
  have h1 := rfp_focus E hdiam k H v z
  have h2 := rfp_wpd_le E k v z
  have h3 := rfp_pw_le_one W k v
  have h4 := rfp_pw_nonneg W k v
  have he : 0 ≤ e := (norm_nonneg _).trans hfocused
  have h5 : W.pathWeight k v * ‖(H v : X) - z‖ ≤ e := by
    calc _ ≤ 1 * e := mul_le_mul h3 hfocused (norm_nonneg _) zero_le_one
      _ = e := one_mul e
  linarith

end

theorem rfp_geom (n : ℕ) : ∑ d ∈ Finset.range n, (1 / 2 : ℝ) ^ (d + 1) = 1 - (1 / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.SwitchingTreeData
open Filter
open scoped Topology BigOperators Pointwise
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {D : NormalizedMinimalData (X := X)}
variable (A : SwitchingTreeData D)
theorem solution (N j : ℕ)
    (hdet : ∀ v : A.tree.TruncationNode N,
      1 - 2 * A.budget (v.1.val + 1) v.2 ≤
        A.functionalAt (v.1.val + 1) v.2
          ((A.nodeLabel (v.1.val + 1) v.2 : X) -
            A.evaluation.evaluate (v.1.val + 1)
              (A.evaluation.idealCutoff (v.1.val + 1) A.anchor (A.terminal j) v.2)))
    (hD : A.evaluation.terminalDefect (N + 1) (A.terminal j) ≤
      A.tree.cumulativeMinimum (OrderedTree.retainedBudget A.label) N)
    (v : A.tree.TruncationNode N) :
    A.weights.pathWeight (v.1.val + 1) v.2 - 5 * A.budget (v.1.val + 1) v.2 ≤
      A.functionalAt (v.1.val + 1) v.2
        ((A.evaluation.beforeBlock v.levelBound (A.nodeLabel N) (A.terminal j) v.2 : X) -
          A.evaluation.afterBlock v.levelBound (A.nodeLabel N) (A.terminal j) v.2) := by
  classical
  let τ := A.tree.tolerance (OrderedTree.retainedBudget A.label)
  have hβ : A.budget (v.1.val + 1) v.2 = OrderedTree.retainedBudget A.label ⟨v.1.val, v.2⟩ := rfl
  have hβpos : 0 < A.budget (v.1.val + 1) v.2 := by
    rw [hβ]; exact candidateBudget_pos _
  have hcm : ∀ d, v.1.val < d → A.tree.cumulativeMinimum (OrderedTree.retainedBudget A.label) d ≤
      A.budget (v.1.val + 1) v.2 := by
    intro d hd
    have := ((A.tree.le_cumulativeMinimum_iff (OrderedTree.retainedBudget A.label) d _).1 le_rfl).2
      v.1.val hd v.2
    rw [hβ]; exact this
  have hτ : (∑ d ∈ Finset.Ico (v.1.val + 1) N, τ d) ≤ A.budget (v.1.val + 1) v.2 := by
    calc (∑ d ∈ Finset.Ico (v.1.val + 1) N, τ d)
        ≤ ∑ d ∈ Finset.Ico (v.1.val + 1) N, (1 / 2 : ℝ) ^ (d + 1) * A.budget (v.1.val + 1) v.2 := by
          refine Finset.sum_le_sum (fun d hd => ?_)
          simp only [τ, OrderedTree.tolerance]
          refine mul_le_mul_of_nonneg_left (hcm d ?_) (by positivity)
          simp only [Finset.mem_Ico] at hd; omega
      _ = (∑ d ∈ Finset.Ico (v.1.val + 1) N, (1 / 2 : ℝ) ^ (d + 1)) * A.budget (v.1.val + 1) v.2 := by
          rw [Finset.sum_mul]
      _ ≤ 1 * A.budget (v.1.val + 1) v.2 := by
          refine mul_le_mul_of_nonneg_right ?_ hβpos.le
          calc (∑ d ∈ Finset.Ico (v.1.val + 1) N, (1 / 2 : ℝ) ^ (d + 1))
              ≤ ∑ d ∈ Finset.range N, (1 / 2 : ℝ) ^ (d + 1) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
                intro d hd; simp only [Finset.mem_Ico, Finset.mem_range] at hd ⊢; omega
            _ = 1 - (1 / 2) ^ N := rfp_geom N
            _ ≤ 1 := by have : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
                        linarith
      _ = A.budget (v.1.val + 1) v.2 := one_mul _
  have hterm : A.evaluation.terminalDefect N (A.terminal j) ≤ A.budget (v.1.val + 1) v.2 := by
    have h1 : A.evaluation.terminalDefect N (A.terminal j) ≤
        A.evaluation.terminalDefect (N + 1) (A.terminal j) := by
      unfold TreeEvaluation.terminalDefect
      rw [Finset.sum_range_succ]
      have : 0 ≤ ∑ v : A.tree.Node N, ‖(A.evaluation.map N v (A.terminal j) : X) - A.terminal j‖ :=
        Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      linarith
    exact h1.trans (hD.trans (hcm N v.1.isLt))
  have hdiam : ∀ a b : D.K, ‖(a : X) - b‖ ≤ 1 := by
    intro p q
    rw [← dist_eq_norm, ← D.diam_one]
    exact Metric.dist_le_diam_of_mem D.bounded p.2 q.2
  -- after block
  have hA : ‖(A.evaluation.afterBlock v.levelBound (A.nodeLabel N) (A.terminal j) v.2 : X) -
      A.evaluation.evaluate (v.1.val + 1)
        (A.evaluation.idealCutoff (v.1.val + 1) A.anchor (A.terminal j) v.2)‖ ≤
      A.budget (v.1.val + 1) v.2 :=
    rfp_after A.evaluation A.anchor (A.terminal j) τ v.levelBound v.2
      (fun d _ p => A.child_average d p) hτ hterm
  -- before block
  have hB : ‖(A.evaluation.beforeBlock v.levelBound (A.nodeLabel N) (A.terminal j) v.2 : X) -
      A.nodeLabel (v.1.val + 1) v.2‖ ≤
      1 - A.weights.pathWeight (v.1.val + 1) v.2 + 2 * A.budget (v.1.val + 1) v.2 := by
    unfold TreeEvaluation.beforeBlock TreeEvaluation.switchRoot
    rw [A.evaluation.evaluate_subtreeOutput v.levelBound]
    refine rfp_before A.evaluation hdiam (v.1.val + 1) _ v.2 _ ?_ ?_
    · rw [rfp_sub_congr' A.evaluation v.levelBound _ (fun s => A.evaluation.map N s A.anchor) v.2
        (fun s hs => by
          simp only [TreeEvaluation.switchLeaves]
          rw [if_pos ((rfp_lt_hi A.tree v.levelBound v.2 s).2 hs.le)]; rfl)]
      exact (rfp_sub_map A.evaluation A.anchor τ v.levelBound
        (fun d _ p => A.child_average d p) v.2).trans hτ
    · exact A.path_displacement v.1.val v.2
  have hdetv := hdet v
  have hf : ‖A.functionalAt (v.1.val + 1) v.2‖ ≤ 1 := A.functional_norm v.1.val v.2
  set φ := A.functionalAt (v.1.val + 1) v.2
  set z : X := (A.nodeLabel (v.1.val + 1) v.2 : X)
  set P : X := (A.evaluation.evaluate (v.1.val + 1)
        (A.evaluation.idealCutoff (v.1.val + 1) A.anchor (A.terminal j) v.2) : X)
  set Bf : X := (A.evaluation.beforeBlock v.levelBound (A.nodeLabel N) (A.terminal j) v.2 : X)
  set Af : X := (A.evaluation.afterBlock v.levelBound (A.nodeLabel N) (A.terminal j) v.2 : X)
  have hsplit : φ (Bf - Af) = φ (z - P) - φ (z - Bf) - φ (Af - P) := by
    rw [← map_sub, ← map_sub]; congr 1; abel
  have hle : ∀ u : X, φ u ≤ ‖u‖ := by
    intro u
    have := φ.le_opNorm u
    have := Real.le_norm_self (φ u)
    nlinarith [norm_nonneg u, norm_nonneg φ]
  have h1 := hle (z - Bf)
  have h2 := hle (Af - P)
  rw [norm_sub_rev] at h1
  rw [hsplit]
  linarith
