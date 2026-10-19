-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.tree_finite_witnesses_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:44:35.212275+00:00
-- url     : https://prove2.me/submissions/3daf2485-720f-445d-9e78-888370890017

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
open scoped Pointwise

theorem rfp_det {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1)
    (y a b : X) (e : ℝ)
    (hya : ‖y - a‖ ≤ 1) (hyb : ‖y - b‖ ≤ 1)
    (ha : 1 - e ≤ f (y - a)) (hb : 1 - e ≤ f (y - b)) :
    |f (a - b)| ≤ e := by
  have h1 : f (y - a) ≤ 1 := by
    have := f.le_opNorm (y - a)
    have := Real.le_norm_self (f (y - a))
    nlinarith [norm_nonneg (y - a), norm_nonneg f]
  have h2 : f (y - b) ≤ 1 := by
    have := f.le_opNorm (y - b)
    have := Real.le_norm_self (f (y - b))
    nlinarith [norm_nonneg (y - b), norm_nonneg f]
  have h3 : f (a - b) = f (y - b) - f (y - a) := by
    rw [← map_sub]; congr 1; abel
  rw [h3, abs_le]; constructor <;> linarith

theorem rfp_tz {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
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

theorem rfp_pd {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {K : Set X} (z : ℕ → K) (hz : DenseRange z) :
    K - K ⊆ closure (Set.range (fun ij : ℕ × ℕ => (z ij.1 : X) - (z ij.2 : X))) := by
  rintro _ ⟨a, ha, c, hc, rfl⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hd := hz
  rw [DenseRange, Metric.dense_iff] at hd
  obtain ⟨_, hz1, ⟨i, rfl⟩⟩ := hd ⟨a, ha⟩ (ε / 2) (by linarith)
  obtain ⟨_, hz2, ⟨j, rfl⟩⟩ := hd ⟨c, hc⟩ (ε / 2) (by linarith)
  refine ⟨(z i : X) - z j, ⟨(i, j), rfl⟩, ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq] at hz1 hz2
  rw [dist_eq_norm] at hz1 hz2 ⊢
  calc ‖a - c - ((z i : X) - z j)‖ = ‖((z i : X) - a) - ((z j : X) - c)‖ := by
        rw [← norm_neg]; congr 1; abel
    _ ≤ ‖(z i : X) - a‖ + ‖(z j : X) - c‖ := norm_sub_le _ _
    _ < ε := by linarith

theorem rfp_wc {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : Set X) (hB : WeaklyCompact B)
    (f : ℕ → X →L[ℝ] ℝ) (c : ℝ)
    (hPrefix : ∀ n : ℕ, ∃ x ∈ B, ∀ i < n, c ≤ f i x) :
    ∃ x ∈ B, ∀ i, c ≤ f i x := by
  let g : ℕ → WeakSpace ℝ X → ℝ := fun i y => (topDualPairing ℝ X).flip y (f i)
  have hg : ∀ i x, g i (toWeakSpace ℝ X x) = f i x := fun i x => rfl
  have hcl : ∀ i, IsClosed {y : WeakSpace ℝ X | c ≤ g i y} := fun i =>
    isClosed_le continuous_const (WeakBilin.eval_continuous (topDualPairing ℝ X).flip (f i))
  obtain ⟨y, hyK, hy⟩ := hB.inter_iInter_nonempty (fun i => {y : WeakSpace ℝ X | c ≤ g i y}) hcl (by
    intro u
    obtain ⟨x, hxB, hx⟩ := hPrefix (u.sup id + 1)
    refine ⟨toWeakSpace ℝ X x, ⟨x, hxB, rfl⟩, ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro i hi
    rw [hg]
    exact hx i (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)))
  obtain ⟨x, hxB, rfl⟩ := hyK
  refine ⟨x, hxB, fun i => ?_⟩
  have := Set.mem_iInter.1 hy i
  simpa [hg] using this

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

theorem rfp_branch (T : OrderedTree) {D : Type*} (B : Set D) (f : (k : ℕ) → T.Node k → D → ℝ)
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

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem solution
    (D : NormalizedMinimalData (X := X)) (T : OrderedTree)
    (f : (k : ℕ) → T.Node k → (X →L[ℝ] ℝ))
    (y : (k : ℕ) → T.Node k → D.K)
    (e : (k : ℕ) → T.Node k → ℝ)
    (hnorm : ∀ k, 0 < k → ∀ v : T.Node k, ‖f k v‖ ≤ 1)
    (hdetector : ∀ k, 0 < k → ∀ v : T.Node k, ∀ i, i < k →
      1 - e k v ≤ f k v ((y k v : X) - (D.z i : X)))
    (hbudget : Summable (fun v : Σ k, T.Node (k + 1) => e (v.1 + 1) v.2))
    (hfinite : ∀ n, 0 < n → ∃ v : T.Node n,
      ∃ d ∈ differenceBall D.K,
        T.DetectsPrefix (fun k v x => f k v x) v d) :
    False := by
  classical
  have h0B : (0 : X) ∈ differenceBall D.K := ⟨Submodule.zero_mem _, by simp⟩
  obtain ⟨b, hbr, hbf⟩ := rfp_branch T (differenceBall D.K) (fun k v x => f k v x) (by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨T.root, 0, h0B, fun i hi hi0 => absurd hi0 (by omega)⟩
    · obtain ⟨v, d, hd, hdet⟩ := hfinite n hn
      exact ⟨v, d, hd, hdet⟩)
  let g : ℕ → X →L[ℝ] ℝ := fun i => f (i + 1) (b (i + 1))
  have hg : ∀ i, ‖g i‖ ≤ 1 := fun i => hnorm (i + 1) (Nat.succ_pos i) _
  obtain ⟨d, hdB, hd⟩ := rfp_wc (differenceBall D.K) D.weak_ball_compact g (1 / 2) (by
    intro n
    obtain ⟨d, hd, hdet⟩ := hbf n
    refine ⟨d, hd, fun i hi => ?_⟩
    have := hdet (i + 1) (by omega) (Nat.succ_pos i)
    simp only at this
    rwa [hbr] at this)
  -- budgets along the branch tend to zero
  have he0 : Tendsto (fun n => e (n + 1) (b (n + 1))) atTop (𝓝 0) := by
    have hinj : Function.Injective (fun n : ℕ => (⟨n, b (n + 1)⟩ : Σ k, T.Node (k + 1))) := by
      intro m n h; simp only [Sigma.mk.inj_iff] at h; exact h.1
    exact (hbudget.comp_injective hinj).tendsto_atTop_zero
  have hdiam : ∀ p q : D.K, ‖(p : X) - q‖ ≤ 1 := by
    intro p q
    rw [← dist_eq_norm, ← D.diam_one]
    exact Metric.dist_le_diam_of_mem D.bounded p.2 q.2
  have hpair : ∀ x ∈ Set.range (fun ij : ℕ × ℕ => (D.z ij.1 : X) - (D.z ij.2 : X)),
      Tendsto (fun n => g n x) atTop (𝓝 0) := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 he0 ε hε
    refine ⟨M + i + j, fun n hn => ?_⟩
    have h1 := hM n (by omega)
    rw [Real.dist_eq, sub_zero] at h1 ⊢
    have hk := rfp_det (g n) (hg n) (y (n + 1) (b (n + 1))) (D.z i) (D.z j) (e (n + 1) (b (n + 1)))
      (hdiam _ _) (hdiam _ _)
      (hdetector (n + 1) (Nat.succ_pos n) _ i (by omega))
      (hdetector (n + 1) (Nat.succ_pos n) _ j (by omega))
    exact lt_of_le_of_lt hk (lt_of_le_of_lt (le_abs_self _) h1)
  have hspan : d ∈ (Submodule.span ℝ (Set.range (fun ij : ℕ × ℕ => (D.z ij.1 : X) - (D.z ij.2 : X)))).topologicalClosure := by
    have hsub : Submodule.span ℝ (D.K - D.K) ≤
        (Submodule.span ℝ (Set.range (fun ij : ℕ × ℕ => (D.z ij.1 : X) - (D.z ij.2 : X)))).topologicalClosure := by
      rw [Submodule.span_le]
      intro x hx
      have := rfp_pd D.z D.dense_z hx
      exact closure_mono (Submodule.subset_span) this
    have := Submodule.topologicalClosure_minimal _ hsub (Submodule.isClosed_topologicalClosure _)
    exact this hdB.1
  have ht := rfp_tz g hg hpair hspan
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  obtain ⟨n, hn⟩ := hev.exists
  linarith [hd n]
