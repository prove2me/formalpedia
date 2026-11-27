-- Prove2me | solution 1 for MetricTSPSublinear.claim_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:47:09.740085+00:00
-- url     : https://prove2.me/submissions/7beecc3b-ceec-4cb0-9355-776c4ec87413

import Mathlib
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost
import Theorems.Thm_CombOpt_TJoin_theorem_5_28
import Theorems.Thm_MetricTSP_tour_of_parity_join


namespace MTSPBridge
open Finset CombOpt.SpanningTree

variable {n : ℕ}

lemma isMetricCost_of_isMetric {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) :
    MetricTSP.IsMetricCost d :=
  ⟨hd.2.1, fun v => (hd.1 v v).2 rfl, fun u v w => hd.2.2 u v w⟩

lemma dist_nonneg' {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (u v : Fin n) :
    0 ≤ d u v := by
  have h := hd.2.2 u v u
  rw [(hd.1 u u).2 rfl, hd.2.1 v u] at h
  linarith

lemma edgeCost_mk {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (u v : Fin n) :
    DoublingMST.edgeCost d s(u, v) = d u v := by
  show min (d u v) (d v u) = d u v
  rw [hd.2.1 v u, min_self]

lemma edgeCost_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (e : Sym2 (Fin n)) :
    0 ≤ DoublingMST.edgeCost d e := by
  induction e with
  | _ u v => rw [edgeCost_mk hd]; exact dist_nonneg' hd u v

lemma edgeCost_diag {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (a : Fin n) :
    DoublingMST.edgeCost d s(a, a) = 0 := by
  rw [edgeCost_mk hd]; exact (hd.1 a a).2 rfl

lemma pairCost_eq_edgeCost {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (e : Sym2 (Fin n)) :
    MetricTSP.pairCost d e = DoublingMST.edgeCost d e := by
  induction e with
  | _ u v =>
    rw [edgeCost_mk hd]
    show (d u v + d v u) / 2 = d u v
    rw [hd.2.1 v u]; ring

/-! ### Walks -/

/-- A Mathlib walk as a walk of the complete graph. -/
noncomputable def ofWalk {G : SimpleGraph (Fin n)} :
    {u v : Fin n} → G.Walk u v → (DoublingMST.completeGraph n).Walk u v
  | _, _, SimpleGraph.Walk.nil => Graph.Walk.nil _
  | u, _, SimpleGraph.Walk.cons (v := w) _ p => Graph.Walk.cons s(u, w) rfl (ofWalk p)

lemma ofWalk_edges {G : SimpleGraph (Fin n)} {u v : Fin n} (p : G.Walk u v) :
    (ofWalk p).edges = p.edges := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [ofWalk, Graph.Walk.edges, SimpleGraph.Walk.edges_cons, ih]

/-- A walk of the complete graph whose edges are edges of `G`, as a Mathlib walk of `G`. -/
noncomputable def toWalk (G : SimpleGraph (Fin n)) :
    {u v : Fin n} → (p : (DoublingMST.completeGraph n).Walk u v) →
      (∀ e ∈ p.edges, e ∈ G.edgeSet) → G.Walk u v
  | _, _, Graph.Walk.nil _, _ => SimpleGraph.Walk.nil
  | _, _, Graph.Walk.cons e h p, hp =>
      SimpleGraph.Walk.cons
        (by
          have he : e ∈ G.edgeSet := hp e (by simp [Graph.Walk.edges])
          have h' : e = _ := h
          rw [h'] at he
          exact (SimpleGraph.mem_edgeSet G).mp he)
        (toWalk G p (fun e' he' => hp e' (by simp [Graph.Walk.edges, he'])))

lemma toWalk_edges (G : SimpleGraph (Fin n)) {u v : Fin n}
    (p : (DoublingMST.completeGraph n).Walk u v) (hp : ∀ e ∈ p.edges, e ∈ G.edgeSet) :
    (toWalk G p hp).edges = p.edges := by
  induction p with
  | nil => rfl
  | cons e h p ih =>
    have h' : e = _ := h
    rw [toWalk, SimpleGraph.Walk.edges_cons, Graph.Walk.edges, ih, h']

lemma toWalk_support (G : SimpleGraph (Fin n)) {u v : Fin n}
    (p : (DoublingMST.completeGraph n).Walk u v) (hp : ∀ e ∈ p.edges, e ∈ G.edgeSet) :
    (toWalk G p hp).support = p.support := by
  induction p with
  | nil => rfl
  | cons e h p ih =>
    rw [toWalk, SimpleGraph.Walk.support_cons, Graph.Walk.support, ih]

lemma tail_nodup_of_dropLast_nodup {α : Type*} (v : α) (t : List α) (ht : t ≠ [])
    (hlast : t.getLast ht = v) (h : (v :: t).dropLast.Nodup) : t.Nodup := by
  rw [List.dropLast_cons_of_ne_nil ht] at h
  have ht' : t = t.dropLast ++ [v] := by
    conv_lhs => rw [← List.dropLast_append_getLast ht]
    rw [hlast]
  rw [ht']
  exact (List.perm_append_singleton v t.dropLast).nodup_iff.mpr h

open Classical in
/-- The edges of a Mathlib tree form a spanning tree of the complete graph. -/
theorem isSpanningTree_of_isTree (G : SimpleGraph (Fin n)) (hG : G.IsTree) :
    (DoublingMST.completeGraph n).IsSpanningTree G.edgeSet.toFinset := by
  classical
  constructor
  · intro u v
    obtain ⟨p⟩ := hG.connected.preconnected u v
    refine ⟨ofWalk p, ?_⟩
    intro e he
    rw [ofWalk_edges] at he
    rw [Set.mem_toFinset]
    exact p.edges_subset_edgeSet he
  · rintro ⟨v, p, hcirc, hsub⟩
    have hp : ∀ e ∈ p.edges, e ∈ G.edgeSet := fun e he => by
      have := hsub e he
      rwa [Set.mem_toFinset] at this
    obtain ⟨q, hqe, hqs⟩ : ∃ q : G.Walk v v, q.edges = p.edges ∧ q.support = p.support :=
      ⟨toWalk G p hp, toWalk_edges G p hp, toWalk_support G p hp⟩
    apply hG.isAcyclic q
    rw [SimpleGraph.Walk.isCycle_def]
    obtain ⟨hnd, hdl, hlen⟩ := hcirc
    have hlen' : 1 ≤ q.length := by rw [← SimpleGraph.Walk.length_edges, hqe]; exact hlen
    have hne : q ≠ SimpleGraph.Walk.nil := by
      intro h
      rw [h] at hlen'
      simp at hlen'
    refine ⟨?_, hne, ?_⟩
    · rw [SimpleGraph.Walk.isTrail_def, hqe]; exact hnd
    · have hsupp : q.support = v :: q.support.tail := (q.cons_tail_support).symm
      have htne : q.support.tail ≠ [] := by
        intro h
        have hl := q.length_support
        rw [hsupp, h] at hl
        simp only [List.length_cons, List.length_nil] at hl
        omega
      have hgl : ∀ (L : List (Fin n)) (hL : L ≠ []) (ht : L.tail ≠ []),
          L.getLast hL = L.tail.getLast ht := by
        intro L hL ht
        cases L with
        | nil => exact absurd rfl hL
        | cons a t => exact List.getLast_cons ht
      apply tail_nodup_of_dropLast_nodup v q.support.tail htne
      · rw [← hgl q.support (by simp) htne]
        exact q.getLast_support
      · rw [← hsupp, hqs]; exact hdl

/-- A forest contains no loop. -/
lemma not_isDiag_of_isForest {T : Finset (Sym2 (Fin n))}
    (hT : (DoublingMST.completeGraph n).IsForest T) {e : Sym2 (Fin n)} (he : e ∈ T) :
    ¬ e.IsDiag := by
  intro hdiag
  induction e with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at hdiag
    subst hdiag
    apply hT
    refine ⟨a, Graph.Walk.cons s(a, a) rfl (Graph.Walk.nil a), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [Graph.Walk.edges]
      · simp [Graph.Walk.support]
      · simp [Graph.Walk.edges]
    · intro e he
      simp [Graph.Walk.edges] at he
      rw [he]; exact he ▸ ‹s(a, a) ∈ T›

/-- A walk from inside `A` to outside `A` uses an edge of the cut `δ(A)`. -/
lemma walk_crosses (A : Finset (Fin n)) {u v : Fin n} (p : (DoublingMST.completeGraph n).Walk u v)
    (hu : u ∈ A) (hv : v ∉ A) : ∃ e ∈ p.edges, e ∈ MetricTSPSublinear.cutEdges univ A := by
  classical
  induction p with
  | nil => exact absurd hu hv
  | @cons a b c e h p ih =>
    by_cases hb : b ∈ A
    · obtain ⟨e', he', hcut⟩ := ih hb hv
      exact ⟨e', by simp [Graph.Walk.edges, he'], hcut⟩
    · refine ⟨e, by simp [Graph.Walk.edges], ?_⟩
      have h' : e = s(a, b) := h
      rw [h']
      unfold MetricTSPSublinear.cutEdges
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨hu, by simp [hb]⟩, rfl⟩

/-- The cut sum over unordered pairs as a double sum over ordered pairs. -/
lemma cut_sum (A : Finset (Fin n)) (x : Sym2 (Fin n) → ℝ) :
    ∑ e ∈ MetricTSPSublinear.cutEdges univ A, x e = ∑ u ∈ A, ∑ v ∈ Aᶜ, x s(u, v) := by
  classical
  unfold MetricTSPSublinear.cutEdges
  rw [Finset.sum_image]
  · rw [Finset.compl_eq_univ_sdiff, Finset.sum_product]
  · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at hab hab'
    simp only at heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · exfalso; rw [h1] at hab; exact hab'.2 hab.1

/-- Double sum over ordered pairs versus sum over unordered non-diagonal pairs. -/
lemma double_sum_sym2 (g : Sym2 (Fin n) → ℝ) (hg : ∀ a, g s(a, a) = 0) :
    ∑ u, ∑ v, g s(u, v) = 2 * ∑ e ∈ MetricTSPSublinear.pairsIn (univ : Finset (Fin n)), g e := by
  classical
  unfold MetricTSPSublinear.pairsIn
  rw [Finset.sum_sym2_filter_not_isDiag]
  rw [← Finset.sum_product']
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ ×ˢ univ : Finset (Fin n × Fin n))
    (fun p => p.1 < p.2) (fun p => g s(p.1, p.2))
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2))
    (fun p => p.2 < p.1) (fun p => g s(p.1, p.2))
  have hdiag0 : ∑ p ∈ ((univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2)).filter
      (fun p => ¬ p.2 < p.1), g s(p.1, p.2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Finset.mem_filter] at hp
    have : p.1 = p.2 := le_antisymm (not_lt.mp hp.2) (not_lt.mp hp.1.2)
    rw [this, hg]
  have hswap : ∑ p ∈ ((univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2)).filter
      (fun p => p.2 < p.1), g s(p.1, p.2)
      = ∑ p ∈ (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), g s(p.1, p.2) := by
    apply Finset.sum_nbij' Prod.swap Prod.swap
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
      exact hp.2
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨not_lt.mpr (le_of_lt hp), hp⟩
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; simp [Sym2.eq_swap]
  have hoff : (univ : Finset (Fin n)).offDiag.filter (fun i => i.1 < i.2)
      = (univ ×ˢ univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product, Finset.mem_univ,
      true_and]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
  rw [hoff, ← hsplit, ← hsplit2, hdiag0, hswap]
  ring

end MTSPBridge



namespace MTSPBridge
open Finset CombOpt.SpanningTree

variable {n : ℕ}

/-- The complete graph has a spanning tree. -/
lemma exists_spanningTree (n : ℕ) :
    ∃ T : Finset (Sym2 (Fin n)), (DoublingMST.completeGraph n).IsSpanningTree T := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨∅, ?_, ?_⟩
    · intro u; exact u.elim0
    · rintro ⟨v, _⟩; exact v.elim0
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨TT, _, hTT⟩ := (SimpleGraph.connected_top : (⊤ : SimpleGraph (Fin n)).Connected).exists_isTree_le
    exact ⟨_, isSpanningTree_of_isTree TT hTT⟩

/-- An MST exists and realizes `mstWeight`. -/
lemma exists_mst (d : Fin n → Fin n → ℝ) :
    ∃ E : Finset (Sym2 (Fin n)), (DoublingMST.completeGraph n).IsSpanningTree E ∧
      DoublingMST.treeWeight d E = DoublingMST.mstWeight d ∧
      ∀ T, (DoublingMST.completeGraph n).IsSpanningTree T →
        DoublingMST.treeWeight d E ≤ DoublingMST.treeWeight d T := by
  classical
  set S := (univ : Finset (Finset (Sym2 (Fin n)))).filter
    (fun T => (DoublingMST.completeGraph n).IsSpanningTree T) with hS
  obtain ⟨T0, hT0⟩ := exists_spanningTree n
  have hSne : S.Nonempty := ⟨T0, by simp [hS, hT0]⟩
  obtain ⟨E, hE, hmin⟩ := Finset.exists_min_image S (DoublingMST.treeWeight d) hSne
  have hEsp : (DoublingMST.completeGraph n).IsSpanningTree E := by simpa [hS] using hE
  have hmin' : ∀ T, (DoublingMST.completeGraph n).IsSpanningTree T →
      DoublingMST.treeWeight d E ≤ DoublingMST.treeWeight d T :=
    fun T hT => hmin T (by simp [hS, hT])
  refine ⟨E, hEsp, ?_, hmin'⟩
  unfold DoublingMST.mstWeight
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨E, hEsp, rfl⟩, ?_⟩
  rintro w ⟨T, hT, rfl⟩
  exact hmin' T hT

lemma mstWeight_le (d : Fin n → Fin n → ℝ) (T : Finset (Sym2 (Fin n)))
    (hT : (DoublingMST.completeGraph n).IsSpanningTree T) :
    DoublingMST.mstWeight d ≤ DoublingMST.treeWeight d T := by
  obtain ⟨E, _, hEw, hmin⟩ := exists_mst d
  rw [← hEw]; exact hmin T hT

/-- A spanning tree crosses every proper nonempty cut. -/
lemma tree_indicator_feasible (T : Finset (Sym2 (Fin n)))
    (hT : (DoublingMST.completeGraph n).IsSpanningTree T) :
    MetricTSPSublinear.IsCutFeasible univ (fun e => if e ∈ T then (1 : ℝ) else 0) := by
  classical
  refine ⟨fun e => by dsimp only; split_ifs <;> norm_num, ?_⟩
  intro A _ hAne hAS
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ : ∃ b, b ∉ A := by
    by_contra h
    push_neg at h
    exact hAS (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨p, hp⟩ := hT.1 a b
  obtain ⟨e, he, hcut⟩ := walk_crosses A p ha hb
  have heT := hp e he
  calc (1 : ℝ) = (if e ∈ T then (1 : ℝ) else 0) := by simp [heT]
    _ ≤ ∑ e ∈ MetricTSPSublinear.cutEdges univ A, (if e ∈ T then (1 : ℝ) else 0) :=
        Finset.single_le_sum (f := fun e => if e ∈ T then (1 : ℝ) else 0)
          (fun e _ => by split_ifs <;> norm_num) hcut

lemma tree_indicator_cost {d : Fin n → Fin n → ℝ} (T : Finset (Sym2 (Fin n)))
    (hT : (DoublingMST.completeGraph n).IsSpanningTree T) :
    ∑ e ∈ MetricTSPSublinear.pairsIn univ, DoublingMST.edgeCost d e * (if e ∈ T then (1 : ℝ) else 0)
      = DoublingMST.treeWeight d T := by
  classical
  unfold DoublingMST.treeWeight
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  simp only [Finset.mem_filter, MetricTSPSublinear.pairsIn, Finset.mem_sym2_iff, Finset.mem_univ,
    implies_true, true_and]
  exact ⟨fun h => h.2, fun h => ⟨not_isDiag_of_isForest hT.2 h, h⟩⟩

lemma cutLP_obj_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (S : Finset (Fin n))
    (x : Sym2 (Fin n) → ℝ) (hx : MetricTSPSublinear.IsCutFeasible S x) :
    0 ≤ ∑ e ∈ MetricTSPSublinear.pairsIn S, DoublingMST.edgeCost d e * x e :=
  Finset.sum_nonneg (fun e _ => mul_nonneg (edgeCost_nonneg hd e) (hx.1 e))

lemma cutLP_le {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (S : Finset (Fin n))
    (x : Sym2 (Fin n) → ℝ) (hx : MetricTSPSublinear.IsCutFeasible S x) :
    MetricTSPSublinear.cutLP d S ≤ ∑ e ∈ MetricTSPSublinear.pairsIn S, DoublingMST.edgeCost d e * x e := by
  unfold MetricTSPSublinear.cutLP
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨y, hy, rfl⟩
    exact cutLP_obj_nonneg hd S y hy
  · exact ⟨x, hx, rfl⟩

lemma feasible_nonempty (S : Finset (Fin n)) :
    ∃ x, MetricTSPSublinear.IsCutFeasible S x := by
  classical
  refine ⟨fun _ => 1, fun _ => zero_le_one, ?_⟩
  intro A hAS hAne hAneS
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hbS, hbA⟩ : ∃ b ∈ S, b ∉ A := by
    by_contra h
    push_neg at h
    exact hAneS (Finset.Subset.antisymm hAS h)
  have hmem : s(a, b) ∈ MetricTSPSublinear.cutEdges S A :=
    Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, Finset.mem_sdiff.mpr ⟨hbS, hbA⟩⟩, rfl⟩
  calc (1 : ℝ) ≤ ∑ e ∈ MetricTSPSublinear.cutEdges S A, (fun _ => (1 : ℝ)) e :=
        Finset.single_le_sum (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) hmem

lemma le_cutLP {d : Fin n → Fin n → ℝ} (S : Finset (Fin n)) (r : ℝ)
    (h : ∀ x, MetricTSPSublinear.IsCutFeasible S x →
      r ≤ ∑ e ∈ MetricTSPSublinear.pairsIn S, DoublingMST.edgeCost d e * x e) :
    r ≤ MetricTSPSublinear.cutLP d S := by
  unfold MetricTSPSublinear.cutLP
  obtain ⟨x0, hx0⟩ := feasible_nonempty S
  refine le_csInf ⟨_, ⟨x0, hx0, rfl⟩⟩ ?_
  rintro t ⟨x, hx, rfl⟩
  exact h x hx

end MTSPBridge



namespace MTSPBridge
open Finset CombOpt.SpanningTree

variable {n : ℕ}

/-- The optimal tour cost is attained. -/
lemma exists_opt_tour (d : Fin n → Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), MetricTSP.tspOpt d = MetricTSP.tourCost d π ∧
      ∀ σ, MetricTSP.tourCost d π ≤ MetricTSP.tourCost d σ := by
  classical
  obtain ⟨π, _, hmin⟩ := Finset.exists_min_image (univ : Finset (Equiv.Perm (Fin n)))
    (MetricTSP.tourCost d) ⟨1, mem_univ _⟩
  refine ⟨π, ?_, fun σ => hmin σ (mem_univ _)⟩
  unfold MetricTSP.tspOpt
  apply IsLeast.csInf_eq
  refine ⟨⟨π, rfl⟩, ?_⟩
  rintro t ⟨σ, rfl⟩
  exact hmin σ (mem_univ _)

lemma tspOpt_le (d : Fin n → Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    MetricTSP.tspOpt d ≤ MetricTSP.tourCost d σ := by
  obtain ⟨π, h1, h2⟩ := exists_opt_tour d
  rw [h1]; exact h2 σ

/-- The tour edges. -/
def tourEdge (π : Equiv.Perm (Fin n)) (i : Fin n) : Sym2 (Fin n) := s(π i, π (finRotate n i))

lemma tour_cost_eq {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (π : Equiv.Perm (Fin n)) :
    MetricTSP.tourCost d π = ∑ i, DoublingMST.edgeCost d (tourEdge π i) := by
  unfold MetricTSP.tourCost tourEdge
  apply Finset.sum_congr rfl; intro i _
  rw [edgeCost_mk hd]

/-- Iterating the rotation. -/
lemma finRotate_iter_val (m : ℕ) (k : ℕ) (i : Fin (m + 1)) :
    ((finRotate (m + 1))^[k] i).val = (i.val + k) % (m + 1) := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', finRotate_apply, Fin.val_add, ih, Fin.val_one']
    rw [← Nat.add_mod, Nat.add_assoc]

lemma finRotate_iter_hit (m : ℕ) (i j : Fin (m + 1)) :
    (finRotate (m + 1))^[j.val + (m + 1) - i.val] i = j := by
  apply Fin.ext
  rw [finRotate_iter_val]
  have h1 : i.val + (j.val + (m + 1) - i.val) = j.val + (m + 1) := by
    have := i.isLt; omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

/-- A cyclic order that starts inside `P` and visits a point outside `P` leaves `P` somewhere. -/
lemma exists_exit (π : Equiv.Perm (Fin n)) (P : Fin n → Prop)
    (hP : ∃ i, P (π i)) (hnP : ∃ i, ¬ P (π i)) :
    ∃ i, P (π i) ∧ ¬ P (π (finRotate n i)) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ := hP
  obtain ⟨j, hj⟩ := hnP
  cases n with
  | zero => exact i0.elim0
  | succ m =>
    have hall : ∀ k : ℕ, P (π ((finRotate (m + 1))^[k] i0)) := by
      intro k
      induction k with
      | zero => simpa using hi0
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hcon _ ih
    have := hall (j.val + (m + 1) - i0.val)
    rw [finRotate_iter_hit] at this
    exact hj this

/-- The tour graph. -/
noncomputable def tourGraph (π : Equiv.Perm (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (Set.range (tourEdge π))

lemma tourGraph_connected (π : Equiv.Perm (Fin n)) (hn : 0 < n) : (tourGraph π).Connected := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hstep : ∀ i, (tourGraph π).Reachable (π i) (π (finRotate n i)) := by
    intro i
    by_cases h : π i = π (finRotate n i)
    · rw [h]
    · apply SimpleGraph.Adj.reachable
      rw [tourGraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨i, rfl⟩, h⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hall : ∀ k : ℕ, (tourGraph π).Reachable (π 0) (π ((finRotate (m + 1))^[k] 0)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (hstep _)
  have hv : ∀ v, (tourGraph π).Reachable (π 0) v := by
    intro v
    have := hall ((π.symm v).val + (m + 1) - (0 : Fin (m + 1)).val)
    rw [finRotate_iter_hit] at this
    simpa using this
  exact SimpleGraph.Connected.mk (fun u v => (hv u).symm.trans (hv v))

/-- `M ≤ TSP`. -/
theorem mst_le_tour {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (π : Equiv.Perm (Fin n)) :
    DoublingMST.mstWeight d ≤ MetricTSP.tourCost d π := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : DoublingMST.mstWeight d ≤ DoublingMST.treeWeight d ∅ :=
      mstWeight_le d ∅ ⟨fun u => u.elim0, by rintro ⟨v, _⟩; exact v.elim0⟩
    simp [DoublingMST.treeWeight] at h0
    simp [MetricTSP.tourCost]; exact h0
  · obtain ⟨TT, hle, hTT⟩ := (tourGraph_connected π hn).exists_isTree_le
    have h1 := mstWeight_le d _ (isSpanningTree_of_isTree TT hTT)
    refine le_trans h1 ?_
    rw [tour_cost_eq hd]
    unfold DoublingMST.treeWeight
    calc ∑ e ∈ TT.edgeSet.toFinset, DoublingMST.edgeCost d e
        ≤ ∑ e ∈ univ.image (tourEdge π), DoublingMST.edgeCost d e := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro e he
            rw [Set.mem_toFinset] at he
            have := SimpleGraph.edgeSet_mono hle he
            rw [tourGraph, SimpleGraph.edgeSet_fromEdgeSet] at this
            obtain ⟨⟨i, rfl⟩, _⟩ := this
            exact Finset.mem_image_of_mem _ (mem_univ i)
          · intro e _ _; exact edgeCost_nonneg hd e
      _ ≤ ∑ i, DoublingMST.edgeCost d (tourEdge π i) :=
          Finset.sum_image_le_of_nonneg (fun e _ => edgeCost_nonneg hd e)

/-- `2K ≤ TSP`. -/
theorem two_cutLP_le_tour {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d)
    (π : Equiv.Perm (Fin n)) :
    2 * MetricTSPSublinear.cutLP d univ ≤ MetricTSP.tourCost d π := by
  classical
  set x : Sym2 (Fin n) → ℝ := fun e => (1 / 2 : ℝ) * ∑ i, (if tourEdge π i = e then (1 : ℝ) else 0)
    with hx
  have hxnn : ∀ e, 0 ≤ x e := fun e => by
    rw [hx]; apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  have hsum : ∀ F : Finset (Sym2 (Fin n)), ∀ g : Sym2 (Fin n) → ℝ,
      ∑ e ∈ F, g e * x e = (1 / 2 : ℝ) * ∑ i, (if tourEdge π i ∈ F then g (tourEdge π i) else 0) := by
    intro F g
    rw [hx]
    simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_ite_eq]
    split_ifs <;> ring
  have hfeas : MetricTSPSublinear.IsCutFeasible univ x := by
    refine ⟨hxnn, ?_⟩
    intro A _ hAne hAU
    obtain ⟨a, ha⟩ := hAne
    obtain ⟨b, hb⟩ : ∃ b, b ∉ A := by
      by_contra h; push_neg at h; exact hAU (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨i, hi1, hi2⟩ := exists_exit π (· ∈ A)
      ⟨π.symm a, by show π (π.symm a) ∈ A; simpa using ha⟩
      ⟨π.symm b, by show ¬ π (π.symm b) ∈ A; simpa using hb⟩
    obtain ⟨j, hj1, hj2⟩ := exists_exit π (· ∉ A)
      ⟨π.symm b, by show ¬ π (π.symm b) ∈ A; simpa using hb⟩
      ⟨π.symm a, by show ¬ ¬ π (π.symm a) ∈ A; simpa using ha⟩
    simp only [not_not] at hj2
    have hij : i ≠ j := by rintro rfl; exact hj1 hi1
    have hmem : ∀ k, (π k ∈ A ∧ π (finRotate n k) ∉ A) ∨ (π k ∉ A ∧ π (finRotate n k) ∈ A) →
        tourEdge π k ∈ MetricTSPSublinear.cutEdges univ A := by
      intro k hk
      unfold MetricTSPSublinear.cutEdges tourEdge
      rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Finset.mem_image.mpr ⟨(π k, π (finRotate n k)), Finset.mem_product.mpr ⟨h1, Finset.mem_sdiff.mpr ⟨mem_univ _, h2⟩⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨(π (finRotate n k), π k), Finset.mem_product.mpr ⟨h2, Finset.mem_sdiff.mpr ⟨mem_univ _, h1⟩⟩, Sym2.eq_swap⟩
    have hcard : 2 ≤ (univ.filter (fun k => tourEdge π k ∈ MetricTSPSublinear.cutEdges univ A)).card := by
      have hsub : ({i, j} : Finset (Fin n)) ⊆
          univ.filter (fun k => tourEdge π k ∈ MetricTSPSublinear.cutEdges univ A) := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rw [Finset.mem_filter]
        refine ⟨mem_univ _, ?_⟩
        rcases hk with rfl | rfl
        · exact hmem _ (Or.inl ⟨hi1, hi2⟩)
        · exact hmem _ (Or.inr ⟨hj1, hj2⟩)
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair hij] at this
    have h := hsum (MetricTSPSublinear.cutEdges univ A) (fun _ => 1)
    simp only [one_mul] at h
    rw [h]
    rw [← Finset.sum_filter] at *
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (2 : ℝ) ≤ ((univ.filter (fun k => tourEdge π k ∈ MetricTSPSublinear.cutEdges univ A)).card : ℝ) := by
      exact_mod_cast hcard
    linarith
  have hK := cutLP_le hd univ x hfeas
  rw [hsum] at hK
  rw [tour_cost_eq hd]
  have : (1 / 2 : ℝ) * ∑ i, (if tourEdge π i ∈ MetricTSPSublinear.pairsIn univ then
      DoublingMST.edgeCost d (tourEdge π i) else 0) ≤ (1 / 2 : ℝ) * ∑ i, DoublingMST.edgeCost d (tourEdge π i) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum; intro i _
    split_ifs
    · exact le_refl _
    · exact edgeCost_nonneg hd _
  linarith

end MTSPBridge



namespace MTSPBridge
open Finset

variable {n : ℕ}

/-- The complete graph as a `CombOpt.TJoin.Graph`. -/
def tjG (n : ℕ) : CombOpt.TJoin.Graph (Fin n) (Sym2 (Fin n)) := ⟨id⟩

lemma tjG_cut (S : Finset (Fin n)) :
    (tjG n).cut S = MetricTSPSublinear.cutEdges univ S := by
  classical
  ext e
  unfold CombOpt.TJoin.Graph.cut MetricTSPSublinear.cutEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_product,
    Finset.mem_sdiff, Prod.exists, Finset.mem_compl]
  induction e with
  | _ u v =>
    show ((∃ a ∈ S, a ∈ s(u, v)) ∧ ∃ b, b ∉ S ∧ b ∈ s(u, v)) ↔ _
    constructor
    · rintro ⟨⟨a, ha, haS⟩, ⟨b, hb, hbS⟩⟩
      refine ⟨a, b, ⟨ha, hb⟩, ?_⟩
      rw [Sym2.mem_iff] at haS hbS
      rcases haS with rfl | rfl <;> rcases hbS with rfl | rfl
      · exact absurd ha hb
      · rfl
      · exact Sym2.eq_swap
      · exact absurd ha hb
    · rintro ⟨a, b, ⟨ha, hb⟩, hab⟩
      refine ⟨⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩⟩
      · rw [← hab]; exact Sym2.mem_mk_left a b
      · rw [← hab]; exact Sym2.mem_mk_right a b

/-- A minimum `O`-join costs at most the cut LP value. -/
theorem exists_tjoin_le_cutLP {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d)
    (O : Finset (Fin n)) (hO : Even O.card) :
    ∃ J : Finset (Sym2 (Fin n)), (tjG n).IsTJoin O J ∧
      ∑ e ∈ J, DoublingMST.edgeCost d e ≤ MetricTSPSublinear.cutLP d univ := by
  classical
  have hthm := CombOpt.TJoin.theorem_5_28 (tjG n) O hO (DoublingMST.edgeCost d) (edgeCost_nonneg hd)
  -- every cut-feasible point is feasible for (5.33)
  have hfeas : ∀ x, MetricTSPSublinear.IsCutFeasible univ x → (tjG n).IsFeasible533 O x := by
    intro x hx
    refine ⟨?_, hx.1⟩
    intro S hS
    rw [tjG_cut]
    apply hx.2 S (Finset.subset_univ S)
    · by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      subst h; simp at hS
    · intro h
      subst h
      simp only [Finset.univ_inter] at hS
      exact (Nat.not_even_iff_odd.mpr hS) hO
  have hobj : ∀ x : Sym2 (Fin n) → ℝ, ∑ e, DoublingMST.edgeCost d e * x e
      = ∑ e ∈ MetricTSPSublinear.pairsIn univ, DoublingMST.edgeCost d e * x e := by
    intro x
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    unfold MetricTSPSublinear.pairsIn at he
    simp only [Finset.mem_filter, Finset.mem_sym2_iff, Finset.mem_univ, implies_true, true_and,
      not_not] at he
    induction e with
    | _ a b =>
      rw [Sym2.mk_isDiag_iff] at he
      subst he
      rw [edgeCost_diag hd, zero_mul]
  have hlp : ∀ x, MetricTSPSublinear.IsCutFeasible univ x →
      (tjG n).lpValue533 O (DoublingMST.edgeCost d) ≤
        ((∑ e ∈ MetricTSPSublinear.pairsIn univ, DoublingMST.edgeCost d e * x e : ℝ) : EReal) := by
    intro x hx
    unfold CombOpt.TJoin.Graph.lpValue533
    rw [← hobj]
    exact iInf₂_le x (hfeas x hx)
  obtain ⟨x0, hx0⟩ := feasible_nonempty (univ : Finset (Fin n))
  -- some T-join exists
  set Js := (univ : Finset (Finset (Sym2 (Fin n)))).filter (fun J => (tjG n).IsTJoin O J) with hJs
  have hJne : Js.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have htop : (tjG n).minTJoinCost O (DoublingMST.edgeCost d) = ⊤ := by
      unfold CombOpt.TJoin.Graph.minTJoinCost
      apply iInf₂_eq_top.mpr
      intro J hJ
      exfalso
      have : J ∈ Js := by rw [hJs, Finset.mem_filter]; exact ⟨mem_univ _, hJ⟩
      rw [hne] at this; simp at this
    have := hlp x0 hx0
    rw [← hthm, htop] at this
    exact absurd this (by simp)
  obtain ⟨J, hJ, hJmin⟩ := Finset.exists_min_image Js (fun J => ∑ e ∈ J, DoublingMST.edgeCost d e) hJne
  have hJt : (tjG n).IsTJoin O J := by rw [hJs, Finset.mem_filter] at hJ; exact hJ.2
  refine ⟨J, hJt, ?_⟩
  apply le_cutLP
  intro x hx
  have h1 : ((∑ e ∈ J, DoublingMST.edgeCost d e : ℝ) : EReal) ≤
      (tjG n).minTJoinCost O (DoublingMST.edgeCost d) := by
    unfold CombOpt.TJoin.Graph.minTJoinCost
    apply le_iInf₂
    intro J' hJ'
    exact EReal.coe_le_coe_iff.mpr (hJmin J' (by rw [hJs, Finset.mem_filter]; exact ⟨mem_univ _, hJ'⟩))
  have h2 := hlp x hx
  rw [← hthm] at h2
  exact EReal.coe_le_coe_iff.mp (h1.trans h2)

end MTSPBridge



namespace MTSPMatch
open MetricTSP Finset

/-- degree in the simple graph of an edge set = number of non-loop edges at v -/
theorem degree_fromEdgeSet {n : ℕ} (J : Finset (Sym2 (Fin n))) (v : Fin n)
    [Fintype ((SimpleGraph.fromEdgeSet (J : Set (Sym2 (Fin n)))).neighborSet v)] :
    (SimpleGraph.fromEdgeSet (J : Set (Sym2 (Fin n)))).degree v
      = (J.filter (fun e => ¬ e.IsDiag ∧ v ∈ e)).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun w _ => s(v, w)) ?_ ?_ ?_
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.fromEdgeSet_adj] at hw
    simp only [Finset.mem_filter, Sym2.mk_isDiag_iff, Sym2.mem_mk_left, and_true]
    exact ⟨hw.1, hw.2⟩
  · intro a _ b _ h
    exact Sym2.congr_right.mp h
  · intro e he
    simp only [Finset.mem_filter] at he
    obtain ⟨hJ, hd, hv⟩ := he
    refine ⟨Sym2.Mem.other hv, ?_, Sym2.other_spec hv⟩
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.fromEdgeSet_adj, Sym2.other_spec hv]
    refine ⟨hJ, fun h => hd ?_⟩
    rw [← Sym2.other_spec hv, ← h]
    exact Sym2.mk_isDiag_iff.mpr rfl

/-- number of non-loop edges of `J` at `v` -/
def dJ {n : ℕ} (J : Finset (Sym2 (Fin n))) (v : Fin n) : ℕ :=
  (J.filter (fun e => ¬ e.IsDiag ∧ v ∈ e)).card

lemma pairCost_mk {n : ℕ} (c : Fin n → Fin n → ℝ) (a b : Fin n) :
    pairCost c s(a, b) = (c a b + c b a) / 2 := rfl

lemma pairCost_nonneg {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (e : Sym2 (Fin n)) : 0 ≤ pairCost c e := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [pairCost_mk]
    have := hc.2.2 a b a
    rw [hc.2.1] at this
    linarith

lemma walk_le {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    {G : SimpleGraph (Fin n)} :
    ∀ {a b : Fin n} (p : G.Walk a b), c a b ≤ (p.edges.map (pairCost c)).sum
  | _, _, .nil => by simp [hc.2.1]
  | a, b, .cons (v := x) h p => by
      simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
      have h1 := walk_le c hc p
      rw [pairCost_mk, hc.1 x a]
      have h2 := hc.2.2 a x b
      linarith

lemma exists_odd_reach {n : ℕ} (J : Finset (Sym2 (Fin n))) (v : Fin n) (hv : Odd (dJ J v)) :
    ∃ u, u ≠ v ∧ Odd (dJ J u) ∧
      (SimpleGraph.fromEdgeSet (J : Set (Sym2 (Fin n)))).Reachable v u := by
  classical
  set H := SimpleGraph.fromEdgeSet (J : Set (Sym2 (Fin n))) with hH
  have hdeg : ∀ w, H.degree w = dJ J w := fun w => degree_fromEdgeSet J w
  let s : Set (Fin n) := (H.connectedComponentMk v).supp
  have hsub : ∀ w : s, H.neighborSet w ⊆ s := by
    intro w x hx
    have hw := w.2
    simp only [s, SimpleGraph.ConnectedComponent.mem_supp_iff] at hw ⊢
    rw [← hw]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hx).symm
  have hvs : v ∈ s := by simp [s]
  have h1 : Odd ((H.induce s).degree ⟨v, hvs⟩) := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hsub _)]
    rw [hdeg]; exact hv
  obtain ⟨w, hwne, hwodd⟩ := (H.induce s).exists_ne_odd_degree_of_exists_odd_degree _ h1
  rw [SimpleGraph.degree_induce_of_neighborSet_subset (hsub _), hdeg] at hwodd
  refine ⟨w.1, fun h => hwne (Subtype.ext h), hwodd, ?_⟩
  have hw := w.2
  simp only [s, SimpleGraph.ConnectedComponent.mem_supp_iff] at hw
  exact SimpleGraph.ConnectedComponent.eq.mp hw.symm

lemma edges_in_J {n : ℕ} {J : Finset (Sym2 (Fin n))} {a b : Fin n}
    (p : (SimpleGraph.fromEdgeSet (J : Set (Sym2 (Fin n)))).Walk a b) {e : Sym2 (Fin n)}
    (he : e ∈ p.edges) : e ∈ J ∧ ¬ e.IsDiag := by
  have := p.edges_subset_edgeSet he
  rw [SimpleGraph.edgeSet_fromEdgeSet] at this
  exact ⟨this.1, this.2⟩

lemma dJ_split {n : ℕ} (J : Finset (Sym2 (Fin n))) {a b : Fin n}
    (p : (SimpleGraph.fromEdgeSet (J : Set (Sym2 (Fin n)))).Walk a b) (hp : p.IsTrail)
    (w : Fin n) :
    dJ J w = dJ (J \ p.edges.toFinset) w + p.edges.countP (fun e => w ∈ e) := by
  classical
  have hPJ : p.edges.toFinset ⊆ J := fun e he => (edges_in_J p (List.mem_toFinset.mp he)).1
  unfold dJ
  conv_lhs => rw [← Finset.sdiff_union_of_subset hPJ]
  rw [Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter Finset.sdiff_disjoint)]
  congr 1
  have : p.edges.toFinset.filter (fun e => ¬ e.IsDiag ∧ w ∈ e)
      = p.edges.toFinset.filter (fun e => w ∈ e) := by
    apply Finset.filter_congr
    intro e he
    have := (edges_in_J p (List.mem_toFinset.mp he)).2
    tauto
  rw [this, List.filter_toFinset, List.toFinset_card_of_nodup (hp.edges_nodup.filter _),
    List.countP_eq_length_filter]

lemma aux {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c) :
    ∀ N, ∀ J : Finset (Sym2 (Fin n)), J.card = N →
    ∃ f : Fin n → Fin n, (∀ v, f (f v) = v) ∧
      (∀ v, f v ≠ v ↔ Odd (dJ J v)) ∧
      ∑ v, c v (f v) ≤ 2 * ∑ e ∈ J, pairCost c e := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro J hJN
  by_cases hodd : ∃ v, Odd (dJ J v)
  swap
  · push Not at hodd
    refine ⟨id, fun v => rfl, fun v => ?_, ?_⟩
    · simp only [id, ne_eq, not_true_eq_false, false_iff]; exact hodd v
    · simp only [id, hc.2.1, Finset.sum_const_zero]
      have := Finset.sum_nonneg (fun e (_ : e ∈ J) => pairCost_nonneg c hc e)
      linarith
  obtain ⟨v, hv⟩ := hodd
  obtain ⟨u, huv, hu, hreach⟩ := exists_odd_reach J v hv
  obtain ⟨q0⟩ := hreach
  set q := q0.bypass with hq
  have hqp : q.IsPath := q0.bypass_isPath
  set P := q.edges.toFinset with hP
  set J' := J \ P with hJ'
  have hPJ : P ⊆ J := fun e he => (edges_in_J q (List.mem_toFinset.mp he)).1
  have hPne : P.Nonempty := by
    rw [hP, List.toFinset_nonempty_iff]
    intro h
    have : q.length = 0 := by rw [← SimpleGraph.Walk.length_edges, h]; rfl
    exact huv (SimpleGraph.Walk.eq_of_length_eq_zero this).symm
  have hcard : J'.card < N := by
    rw [← hJN]; exact Finset.card_lt_card (Finset.sdiff_ssubset hPJ hPne)
  obtain ⟨f', hf'inv, hf'odd, hf'cost⟩ := ih _ hcard J' rfl
  have hsplit := dJ_split J q hqp.isTrail
  have hev := hqp.isTrail.even_countP_edges_iff
  -- parity facts
  have hpar : ∀ w, w ≠ u → w ≠ v → (Odd (dJ J' w) ↔ Odd (dJ J w)) := by
    intro w hwu hwv
    have h1 := (hev w).mpr (fun _ => ⟨hwv, hwu⟩)
    rw [hsplit w, Nat.odd_add]
    exact ⟨fun h => ⟨fun _ => h1, fun _ => h⟩, fun h => h.2 h1⟩
  have hbv : ¬ Even (q.edges.countP (fun e => v ∈ e)) := by
    rw [hev v]; intro h; exact (h huv.symm).1 rfl
  have hbu : ¬ Even (q.edges.countP (fun e => u ∈ e)) := by
    rw [hev u]; intro h; exact (h huv.symm).2 rfl
  have hfv : f' v = v := by
    by_contra h
    have h2 := (hf'odd v).mp h
    have hv' := hv
    rw [hsplit v, Nat.odd_add] at hv'
    exact hbv (hv'.mp h2)
  have hfu : f' u = u := by
    by_contra h
    have h2 := (hf'odd u).mp h
    have hu' := hu
    rw [hsplit u, Nat.odd_add] at hu'
    exact hbu (hu'.mp h2)
  refine ⟨fun w => if w = v then u else if w = u then v else f' w, ?_, ?_, ?_⟩
  · intro w
    by_cases hwv : w = v
    · subst hwv; simp [huv]
    by_cases hwu : w = u
    · subst hwu; simp [huv]
    have h1 : f' w ≠ v := fun h => hwv (by rw [← hf'inv w, h, hfv])
    have h2 : f' w ≠ u := fun h => hwu (by rw [← hf'inv w, h, hfu])
    simp [hwv, hwu, h1, h2, hf'inv]
  · intro w
    by_cases hwv : w = v
    · subst hwv; simp [huv, hv]
    by_cases hwu : w = u
    · subst hwu; simp [huv, hu, huv.symm]
    simp only [hwv, hwu, if_false]
    rw [hf'odd w]
    exact hpar w hwu hwv
  · have hpt : ∀ w, c w (if w = v then u else if w = u then v else f' w)
        = c w (f' w) + (if w = v then c v u else 0) + (if w = u then c u v else 0) := by
      intro w
      by_cases hwv : w = v
      · subst hwv; simp [huv.symm, hfv, hc.2.1]
      by_cases hwu : w = u
      · subst hwu; simp [hfu, hc.2.1, hwv]
      simp [hwv, hwu]
    rw [Finset.sum_congr rfl (fun w _ => hpt w), Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hsum : ∑ e ∈ J, pairCost c e = ∑ e ∈ J', pairCost c e + ∑ e ∈ P, pairCost c e :=
      (Finset.sum_sdiff hPJ).symm
    have hPsum : ∑ e ∈ P, pairCost c e = (q.edges.map (pairCost c)).sum :=
      List.sum_toFinset _ hqp.isTrail.edges_nodup
    have hw := walk_le c hc q
    rw [hc.1 u v]
    linarith

/-- A T-join can be shortcut to a perfect matching on its odd-degree vertices. -/
theorem matching_of_join {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (J : Finset (Sym2 (Fin n))) :
    ∃ f : Fin n → Fin n, (∀ v, f (f v) = v) ∧
      (∀ v, f v ≠ v ↔ Odd ((J.filter (fun e => ¬ e.IsDiag ∧ v ∈ e)).card)) ∧
      ∑ v, c v (f v) ≤ 2 * ∑ e ∈ J, pairCost c e :=
  aux c hc _ J rfl

end MTSPMatch



namespace MTSPBridge
open Finset CombOpt.SpanningTree

variable {n : ℕ}

lemma reachable_of_walk (F : Finset (Sym2 (Fin n))) {u v : Fin n}
    (p : (DoublingMST.completeGraph n).Walk u v) (hp : ∀ e ∈ p.edges, e ∈ F) :
    (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).Reachable u v := by
  induction p with
  | nil => rfl
  | @cons a b c e h p ih =>
    have he : e = s(a, b) := h
    have heF : e ∈ F := hp e (by simp [Graph.Walk.edges])
    have hrest := ih (fun e' he' => hp e' (by simp [Graph.Walk.edges, he']))
    refine SimpleGraph.Reachable.trans ?_ hrest
    by_cases hab : a = b
    · rw [hab]
    · apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨by rw [← he]; exact heF, hab⟩

lemma mem_tjG_cut_single (v : Fin n) (e : Sym2 (Fin n)) :
    e ∈ (tjG n).cut {v} ↔ ¬ e.IsDiag ∧ v ∈ e := by
  classical
  rw [tjG_cut]
  unfold MetricTSPSublinear.cutEdges
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_singleton, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Prod.exists]
  induction e with
  | _ a b =>
    constructor
    · rintro ⟨x, y, ⟨rfl, hy⟩, hxy⟩
      rw [← hxy]
      exact ⟨by rw [Sym2.mk_isDiag_iff]; exact fun h => hy h.symm, Sym2.mem_mk_left _ _⟩
    · rintro ⟨hd, hv⟩
      rw [Sym2.mk_isDiag_iff] at hd
      rw [Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact ⟨v, b, ⟨rfl, fun h => hd h.symm⟩, rfl⟩
      · exact ⟨v, a, ⟨rfl, fun h => hd h⟩, Sym2.eq_swap⟩

/-- `TSP ≤ M + K` for `n ≥ 3`. -/
theorem tsp_le_mst_add_cutLP_of_three_le {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d)
    (hn : 3 ≤ n) :
    MetricTSP.tspOpt d ≤ DoublingMST.mstWeight d + MetricTSPSublinear.cutLP d univ := by
  classical
  have hc := isMetricCost_of_isMetric hd
  obtain ⟨E, hE, hEw, _⟩ := exists_mst d
  set G : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n))) with hG
  have hGconn : G.Connected := by
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact SimpleGraph.Connected.mk (fun u v => by
      obtain ⟨p, hp⟩ := hE.1 u v
      exact reachable_of_walk E p hp)
  have hdeg : ∀ v, G.degree v = (E.filter (fun e => ¬ e.IsDiag ∧ v ∈ e)).card :=
    fun v => MTSPMatch.degree_fromEdgeSet E v
  set O : Finset (Fin n) := univ.filter (fun v => Odd (G.degree v)) with hO
  have hOeven : Even O.card := G.even_card_odd_degree_vertices
  obtain ⟨J, hJ, hJK⟩ := exists_tjoin_le_cutLP hd O hOeven
  have hJpar : ∀ v, Odd ((J.filter (fun e => ¬ e.IsDiag ∧ v ∈ e)).card) ↔ Odd (G.degree v) := by
    intro v
    have h := hJ v
    have hfil : J ∩ (tjG n).cut {v} = J.filter (fun e => ¬ e.IsDiag ∧ v ∈ e) := by
      ext e; simp [mem_tjG_cut_single]
    rw [hfil] at h
    by_cases hv : Odd (G.degree v)
    · have : O ∩ {v} = {v} := by
        ext w; simp only [Finset.mem_inter, Finset.mem_singleton, hO, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · rintro rfl; exact ⟨hv, rfl⟩
      rw [this, Finset.card_singleton] at h
      simp only [hv, iff_true]
      rw [Nat.odd_iff]; exact h
    · have : O ∩ {v} = ∅ := by
        ext w; simp only [Finset.mem_inter, Finset.mem_singleton, hO, Finset.mem_filter,
          Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
        rintro hw rfl; exact hv hw
      rw [this, Finset.card_empty] at h
      simp only [hv, iff_false]
      rw [Nat.not_odd_iff_even, Nat.even_iff]; exact h
  obtain ⟨f, hinv, hfodd, hfcost⟩ := MTSPMatch.matching_of_join d hc J
  have hodd : ∀ v, f v ≠ v ↔ Odd (G.degree v) := fun v => (hfodd v).trans (hJpar v)
  obtain ⟨π, hπ⟩ := MetricTSP.tour_of_parity_join n hn d hc G hGconn f hinv hodd
  have hGcost : MetricTSP.graphCost d G = DoublingMST.mstWeight d := by
    rw [← hEw]
    unfold MetricTSP.graphCost DoublingMST.treeWeight
    apply Finset.sum_congr
    · ext e
      simp only [Set.mem_toFinset]
      show e ∈ (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).edgeSet ↔ e ∈ E
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
      exact ⟨fun h => h.1, fun h => ⟨h, not_isDiag_of_isForest hE.2 h⟩⟩
    · intro e _; exact pairCost_eq_edgeCost hd e
  have hJcost : ∑ e ∈ J, MetricTSP.pairCost d e = ∑ e ∈ J, DoublingMST.edgeCost d e :=
    Finset.sum_congr rfl (fun e _ => pairCost_eq_edgeCost hd e)
  calc MetricTSP.tspOpt d ≤ MetricTSP.tourCost d π := tspOpt_le d π
    _ ≤ MetricTSP.graphCost d G + (1 / 2) * ∑ v, d v (f v) := hπ
    _ ≤ DoublingMST.mstWeight d + MetricTSPSublinear.cutLP d univ := by
        rw [hGcost]
        have : (1 / 2 : ℝ) * ∑ v, d v (f v) ≤ ∑ e ∈ J, MetricTSP.pairCost d e := by linarith
        linarith

lemma mstWeight_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) :
    0 ≤ DoublingMST.mstWeight d := by
  obtain ⟨E, _, hEw, _⟩ := exists_mst d
  rw [← hEw]
  exact Finset.sum_nonneg (fun e _ => edgeCost_nonneg hd e)

lemma cutLP_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (S : Finset (Fin n)) :
    0 ≤ MetricTSPSublinear.cutLP d S :=
  le_cutLP S 0 (fun x hx => cutLP_obj_nonneg hd S x hx)

/-- `TSP ≤ M + K`. -/
theorem tsp_le_mst_add_cutLP {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) :
    MetricTSP.tspOpt d ≤ DoublingMST.mstWeight d + MetricTSPSublinear.cutLP d univ := by
  classical
  by_cases hn3 : 3 ≤ n
  · exact tsp_le_mst_add_cutLP_of_three_le hd hn3
  have hM := mstWeight_nonneg hd
  have hK := cutLP_nonneg hd (univ : Finset (Fin n))
  have htour := tspOpt_le d 1
  rcases (by omega : n ≤ 1 ∨ n = 2) with hn1 | hn2
  · have h0 : MetricTSP.tourCost d 1 = 0 := by
      unfold MetricTSP.tourCost
      apply Finset.sum_eq_zero
      intro i _
      have : finRotate n i = i := by
        apply Fin.ext; have := (finRotate n i).isLt; have := i.isLt; omega
      rw [this]; exact (hd.1 _ _).2 rfl
    linarith
  · subst hn2
    have h01 : MetricTSP.tourCost d 1 = 2 * d 0 1 := by
      unfold MetricTSP.tourCost
      rw [Fin.sum_univ_two]
      simp [finRotate_apply, hd.2.1 1 0]
      ring
    -- every pair crossing the cut `{0}` is `s(0, 1)`
    have hcut : ∀ e ∈ MetricTSPSublinear.cutEdges univ {(0 : Fin 2)}, e = s(0, 1) := by
      intro e he
      unfold MetricTSPSublinear.cutEdges at he
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_univ,
        true_and] at hab
      obtain ⟨rfl, hb⟩ := hab
      have : b = 1 := by fin_cases b <;> simp_all
      rw [this]
    have hM2 : d 0 1 ≤ DoublingMST.mstWeight d := by
      obtain ⟨E, hE, hEw, _⟩ := exists_mst d
      rw [← hEw]
      obtain ⟨p, hp⟩ := hE.1 0 1
      obtain ⟨e, he, hecut⟩ := walk_crosses {(0 : Fin 2)} p (by simp) (by simp)
      have := hcut e hecut
      subst this
      unfold DoublingMST.treeWeight
      rw [← edgeCost_mk hd]
      exact Finset.single_le_sum (fun e _ => edgeCost_nonneg hd e) (hp _ he)
    have hK2 : d 0 1 ≤ MetricTSPSublinear.cutLP d univ := by
      apply le_cutLP
      intro x hx
      have h1 := hx.2 {(0 : Fin 2)} (Finset.subset_univ _) (by simp) (by decide)
      have hsub : MetricTSPSublinear.cutEdges univ {(0 : Fin 2)} ⊆ MetricTSPSublinear.pairsIn univ := by
        intro e he
        rw [hcut e he]
        unfold MetricTSPSublinear.pairsIn
        simp [Sym2.mk_isDiag_iff]
      calc d 0 1 ≤ d 0 1 * ∑ e ∈ MetricTSPSublinear.cutEdges univ {(0 : Fin 2)}, x e := by
            have := dist_nonneg' hd 0 1
            nlinarith
        _ = ∑ e ∈ MetricTSPSublinear.cutEdges univ {(0 : Fin 2)}, DoublingMST.edgeCost d e * x e := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e he
            rw [hcut e he, edgeCost_mk hd]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun e _ _ => mul_nonneg (edgeCost_nonneg hd e) (hx.1 e))
    linarith

end MTSPBridge

open MTSPBridge in
theorem claim_3_3_sol {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) :
    max (DoublingMST.mstWeight d) (2 * MetricTSPSublinear.cutLP d Finset.univ) ≤ MetricTSP.tspOpt d ∧
      MetricTSP.tspOpt d ≤ DoublingMST.mstWeight d + MetricTSPSublinear.cutLP d Finset.univ := by
  obtain ⟨π, hπ, _⟩ := exists_opt_tour d
  refine ⟨max_le ?_ ?_, tsp_le_mst_add_cutLP hd⟩
  · rw [hπ]; exact mst_le_tour hd π
  · rw [hπ]; exact two_cutLP_le_tour hd π


open scoped Classical
open MetricTSPSublinear

theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) :
    max (DoublingMST.mstWeight d) (2 * cutLP d Finset.univ) ≤ MetricTSP.tspOpt d ∧
      MetricTSP.tspOpt d ≤ DoublingMST.mstWeight d + cutLP d Finset.univ :=
  claim_3_3_sol d hd
