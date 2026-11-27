-- Prove2me | solution 1 for MetricTSPSublinear.corollary_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:34:01.626809+00:00
-- url     : https://prove2.me/submissions/12f6181a-ad6d-4f99-9990-7396072099e8

import Mathlib
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost
import Definitions.Def_MetricTSPSublinear_IsDualFeasible
import Definitions.Def_MetricTSPSublinear_Dominated
import Definitions.Def_MetricTSPSublinear_dualOf
import Theorems.Thm_Polyhedral_lp_strong_duality
import Definitions.Def_MetricTSPSublinear_IsSubtree
import Definitions.Def_MetricTSPSublinear_SteinerTree
import Definitions.Def_MetricTSPSublinear_rdist


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



namespace MTSPTree
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

lemma reach_or_reach_aux {a b : V} : ∀ (w t : V) (p : G.Walk w t), t = a →
    (G.deleteEdges {s(a, b)}).Reachable w a ∨ (G.deleteEdges {s(a, b)}).Reachable w b := by
  intro w t p
  induction p with
  | nil => intro h; subst h; exact Or.inl (Reachable.refl _)
  | @cons u u' _ h p ih =>
    intro ht
    have ih := ih ht
    by_cases he : s(u, u') = s(a, b)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (Reachable.refl _)
      · exact Or.inr (Reachable.refl _)
    · have hadj : (G.deleteEdges {s(a, b)}).Adj u u' := by
        rw [deleteEdges_adj]; exact ⟨h, by simpa using he⟩
      rcases ih with h1 | h1
      · exact Or.inl (hadj.reachable.trans h1)
      · exact Or.inr (hadj.reachable.trans h1)

/-- After deleting a tree edge `{a,b}`, every vertex is still connected to `a` or to `b`. -/
lemma reach_or_reach (hconn : G.Connected) {a b : V} (w : V) :
    (G.deleteEdges {s(a, b)}).Reachable w a ∨ (G.deleteEdges {s(a, b)}).Reachable w b := by
  obtain ⟨p⟩ := hconn.preconnected w a
  exact reach_or_reach_aux w a p rfl

lemma not_reach_of_adj (hac : G.IsAcyclic) {a b : V} (hadj : G.Adj a b) :
    ¬ (G.deleteEdges {s(a, b)}).Reachable a b :=
  isAcyclic_iff_forall_adj_isBridge.mp hac hadj

/-- In a tree, an edge lies on the path between `u` and `v` iff deleting it separates them. -/
lemma mem_path_edges_iff (hT : G.IsTree) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (e : Sym2 V) : e ∈ p.edges ↔ ¬ (G.deleteEdges {e}).Reachable u v := by
  classical
  constructor
  · intro he hR
    obtain ⟨q⟩ := hR
    let q' := q.toPath
    have hq'p : (q'.val.mapLe (G.deleteEdges_le {e})).IsPath := q'.property.mapLe _
    have heq : q'.val.mapLe (G.deleteEdges_le {e}) = p := by
      have := (hT.existsUnique_path u v).unique hq'p hp
      exact this
    rw [← heq, Walk.edges_mapLe_eq_edges] at he
    have := q'.val.edges_subset_edgeSet he
    rw [edgeSet_deleteEdges] at this
    exact this.2 rfl
  · intro hR
    by_contra he
    exact hR ⟨p.toDeleteEdge e he⟩

/-- Reachability classes after deleting an edge of a tree. -/
lemma reach_iff_reach (hT : G.IsTree) {a b : V} (hadj : G.Adj a b) (x p q : V) :
    ((G.deleteEdges {s(a, b)}).Reachable x p ↔ (G.deleteEdges {s(a, b)}).Reachable x q) ↔
      (G.deleteEdges {s(a, b)}).Reachable p q := by
  set R := (G.deleteEdges {s(a, b)}).Reachable with hRdef
  have hab : ¬ R a b := not_reach_of_adj hT.isAcyclic hadj
  have hx := reach_or_reach hT.connected (a := a) (b := b) x
  have hp := reach_or_reach hT.connected (a := a) (b := b) p
  have hq := reach_or_reach hT.connected (a := a) (b := b) q
  constructor
  · intro h
    by_cases hxp : R x p
    · exact hxp.symm.trans (h.mp hxp)
    · have hxq : ¬ R x q := fun hh => hxp (h.mpr hh)
      rcases hx with hx | hx
      · have hpb : R p b := by
          rcases hp with hp | hp
          · exact absurd (hx.trans hp.symm) hxp
          · exact hp
        have hqb : R q b := by
          rcases hq with hq | hq
          · exact absurd (hx.trans hq.symm) hxq
          · exact hq
        exact hpb.trans hqb.symm
      · have hpa : R p a := by
          rcases hp with hp | hp
          · exact hp
          · exact absurd (hx.trans hp.symm) hxp
        have hqa : R q a := by
          rcases hq with hq | hq
          · exact hq
          · exact absurd (hx.trans hq.symm) hxq
        exact hpa.trans hqa.symm
  · intro h
    exact ⟨fun h1 => h1.trans h, fun h1 => h1.trans h.symm⟩

/-- In a finite tree, behind every edge `a → b` (on the side of `b`) there is a vertex of degree
at most one. -/
lemma exists_leaf_behind [Fintype V] [DecidableEq V] (hT : G.IsTree) {a b : V} (hadj : G.Adj a b) :
    ∃ c, (G.deleteEdges {s(a, b)}).Reachable b c ∧ ∀ y₁ y₂, G.Adj c y₁ → G.Adj c y₂ → y₁ = y₂ := by
  classical
  let s : Set ℕ := {k | ∃ (c : V) (q : G.Walk b c), q.IsPath ∧ a ∉ q.support ∧ q.length = k}
  have hfin : s.Finite := Set.Finite.subset (Set.finite_le_nat (Fintype.card V))
    (fun k ⟨_, q, hq, _, hk⟩ => hk ▸ le_of_lt hq.length_lt)
  have hb0 : (0 : ℕ) ∈ s := ⟨b, Walk.nil, Walk.IsPath.nil, by
    simp only [Walk.support_nil, List.mem_singleton]; exact hadj.ne, rfl⟩
  obtain ⟨k, ⟨c, q, hq, haq, hk⟩, hmax⟩ := hfin.exists_maximal ⟨0, hb0⟩
  have hext : ∀ y, G.Adj c y → y ∉ q.support → y ≠ a → False := by
    intro y hcy hy hya
    have hq2 : (q.concat hcy).IsPath := hq.concat hy hcy
    have hmem : (q.concat hcy).length ∈ s := ⟨y, q.concat hcy, hq2, by
      simp only [Walk.support_concat, List.concat_eq_append, List.mem_append, List.mem_singleton,
        not_or]
      exact ⟨haq, fun h => hya h.symm⟩, rfl⟩
    have := hmax hmem (by rw [Walk.length_concat, hk]; omega)
    rw [Walk.length_concat, hk] at this
    omega
  have hRq : (G.deleteEdges {s(a, b)}).Reachable b c := by
    refine ⟨q.toDeleteEdge (s(a, b)) ?_⟩
    intro hmem
    exact haq (q.fst_mem_support_of_mem_edges hmem)
  refine ⟨c, hRq, ?_⟩
  -- every neighbour of `c` is a fixed vertex
  have hnb : ∀ y, G.Adj c y → y = (if c = b then a else q.penultimate) := by
    intro y hcy
    by_cases hcb : c = b
    · subst hcb
      rw [if_pos rfl]
      have hqnil : q = Walk.nil := Walk.isPath_iff_eq_nil.mp hq
      by_contra hya
      apply hext y hcy _ hya
      rw [hqnil, Walk.support_nil, List.mem_singleton]
      exact hcy.ne.symm
    · rw [if_neg hcb]
      by_cases hy : y ∈ q.support
      · exact hT.isAcyclic.eq_penultimate_of_adj_end hq hcy hy
      · by_cases hya : y = a
        · exfalso
          subst hya
          -- two different paths from `y = a` to `c`
          have hP : (Walk.cons hadj q).IsPath := hq.cons haq
          have h1 : (⟨Walk.cons hadj q, hP⟩ : G.Path y c) = Path.singleton hcy.symm :=
            (hT.isAcyclic.subsingleton_path y c).elim _ _
          have hlen := congrArg (fun P : G.Path y c => P.val.length) h1
          simp only [Walk.length_cons, Path.singleton_coe, Walk.length_cons, Walk.length_nil] at hlen
          have : q.length = 0 := by omega
          exact hcb (Walk.eq_of_length_eq_zero this).symm
        · exact absurd (hext y hcy hy hya) id
  intro y₁ y₂ h1 h2
  rw [hnb y₁ h1, hnb y₂ h2]

end MTSPTree



namespace MTSPSteiner
open MetricTSPSublinear SimpleGraph Finset MTSPTree

variable {n : ℕ} {S : Finset (Fin n)}

lemma path_isPath (F : SteinerTree S) (a b : Fin F.m) : (F.T.path a b).IsPath :=
  (F.T.isTree.existsUnique_path a b).exists.choose_spec

lemma mem_edges_iff (F : SteinerTree S) (e : Sym2 (Fin F.m)) : e ∈ F.edges ↔ e ∈ F.T.G.edgeSet := by
  classical
  unfold SteinerTree.edges; simp

/-- The tree distance as a sum over the edges on the path. -/
lemma dist_eq_sum (F : SteinerTree S) (a b : Fin F.m) :
    F.T.dist a b = ∑ e ∈ F.edges, if e ∈ (F.T.path a b).edges then F.T.w e else 0 := by
  classical
  have hp := path_isPath F a b
  have h1 : F.T.dist a b = ((F.T.path a b).edges.map F.T.w).sum := by
    unfold TreeCoverLB.WeightedTree.dist KServer.walkWeight
    rw [Walk.edges, List.map_map]
    rfl
  rw [h1, ← List.sum_toFinset _ hp.isTrail.edges_nodup, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  simp only [List.mem_toFinset, Finset.mem_filter, mem_edges_iff]
  exact ⟨fun h => ⟨(F.T.path a b).edges_subset_edgeSet h, h⟩, fun h => h.2⟩

/-- Separation by the side of an edge = the edge lies on the path. -/
lemma sep_side_iff (F : SteinerTree S) (x₀ u v : Fin n) (e : Sym2 (Fin F.m))
    (he : e ∈ F.T.G.edgeSet) (hu : u ∈ S) (hv : v ∈ S) :
    ¬ ((u ∈ F.side e x₀) ↔ (v ∈ F.side e x₀)) ↔ e ∈ (F.T.path (F.ι u) (F.ι v)).edges := by
  classical
  rw [mem_path_edges_iff F.T.isTree _ (path_isPath F _ _)]
  unfold SteinerTree.side
  simp only [Finset.mem_filter, hu, hv, true_and]
  induction e with
  | _ a b =>
    have hadj : F.T.G.Adj a b := he
    have h := reach_iff_reach F.T.isTree hadj (F.ι x₀) (F.ι u) (F.ι v)
    tauto

/-- The value of the dual of `F` on the cuts separating `u, v` is the tree distance. -/
lemma sep_sum (F : SteinerTree S) (x₀ u v : Fin n) (hu : u ∈ S) (hv : v ∈ S) :
    ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => ¬ ((u ∈ A) ↔ (v ∈ A))), dualOf F x₀ A
      = F.pathWt (F.ι u) (F.ι v) := by
  classical
  unfold dualOf SteinerTree.pathWt
  rw [Finset.sum_comm, dist_eq_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_ite_eq]
  have hsep := sep_side_iff F x₀ u v e ((mem_edges_iff F e).mp he) hu hv
  by_cases h : ¬ ((u ∈ F.side e x₀) ↔ (v ∈ F.side e x₀))
  · rw [if_pos (by simpa using h), if_pos (hsep.mp h)]
  · rw [if_neg (by simpa using h), if_neg (fun hh => h (hsep.mpr hh))]

/-- Every side of an edge of a Steiner tree contains a point of `S`. -/
lemma side_nonempty (F : SteinerTree S) (x₀ : Fin n) (e : Sym2 (Fin F.m))
    (he : e ∈ F.T.G.edgeSet) : (F.side e x₀).Nonempty := by
  classical
  induction e with
  | _ a' b' =>
    have hadj : F.T.G.Adj a' b' := he
    have key : ∀ a b : Fin F.m, F.T.G.Adj a b → s(a, b) = s(a', b') →
        (F.T.G.deleteEdges {s(a, b)}).Reachable (F.ι x₀) a → (F.side s(a', b') x₀).Nonempty := by
      intro a b hab heq hxa
      obtain ⟨c, hbc, hleaf⟩ := exists_leaf_behind F.T.isTree hab
      obtain ⟨s, hs, hsc⟩ := F.leaves c hleaf
      refine ⟨s, ?_⟩
      unfold SteinerTree.side
      rw [Finset.mem_filter, ← heq, hsc]
      refine ⟨hs, fun hxc => ?_⟩
      exact not_reach_of_adj F.T.isTree.isAcyclic hab (hxa.symm.trans (hxc.trans hbc.symm))
    rcases reach_or_reach F.T.isTree.connected (a := a') (b := b') (F.ι x₀) with h | h
    · exact key a' b' hadj rfl h
    · exact key b' a' hadj.symm Sym2.eq_swap (by rw [Sym2.eq_swap]; exact h)

lemma pathWt_self (F : SteinerTree S) (a : Fin F.m) : F.pathWt a a = 0 := by
  classical
  unfold SteinerTree.pathWt
  rw [dist_eq_sum]
  apply Finset.sum_eq_zero
  intro e _
  rw [if_neg]
  rw [mem_path_edges_iff F.T.isTree _ (path_isPath F _ _)]
  exact fun h => h (Reachable.refl _)

theorem claim_4_1_sol (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (F : SteinerTree S) (x₀ : Fin n) (hx₀ : x₀ ∈ S) :
    IsDualFeasible d S (dualOf F x₀) ↔ Dominated d F := by
  classical
  constructor
  · intro hy u hu v hv
    by_cases huv : u = v
    · subst huv
      rw [pathWt_self, (hd.1 u u).2 rfl]
    · rw [← sep_sum F x₀ u v hu hv]
      exact hy.2.2 u hu v hv huv
  · intro hdom
    refine ⟨?_, ?_, ?_⟩
    · intro A
      unfold dualOf
      apply Finset.sum_nonneg
      intro e he
      split_ifs
      · exact F.T.w_nonneg e ((mem_edges_iff F e).mp he)
      · exact le_refl 0
    · intro A hA
      unfold dualOf
      apply Finset.sum_eq_zero
      intro e he
      rw [if_neg]
      intro hside
      apply hA
      subst hside
      refine ⟨Finset.filter_subset _ _, side_nonempty F x₀ e ((mem_edges_iff F e).mp he), ?_⟩
      intro hS
      have : x₀ ∈ F.side e x₀ := by rw [hS]; exact hx₀
      unfold SteinerTree.side at this
      exact (Finset.mem_filter.mp this).2 (Reachable.refl _)
    · intro u hu v hv _
      rw [sep_sum F x₀ u v hu hv]
      exact hdom u hu v hv

end MTSPSteiner



namespace MTSPLamTree
open MetricTSPSublinear SimpleGraph Finset MTSPTree MTSPSteiner

open scoped Classical

section Generic
variable {α V : Type*} [Fintype V]

/-- A laminar family of nonempty sets indexed injectively by `V`, with top element `node r`. -/
structure Lam (node : V → Finset α) (r : V) : Prop where
  inj : Function.Injective node
  top : ∀ v, node v ⊆ node r
  ne : ∀ v, (node v).Nonempty
  lam : ∀ u v, Disjoint (node u) (node v) ∨ node u ⊆ node v ∨ node v ⊆ node u

/-- The parent: a smallest node strictly containing `v` (and `r` for `v = r`). -/
noncomputable def par (node : V → Finset α) (r : V) (v : V) : V :=
  if h : ∃ u, v ≠ r ∧ node v ⊂ node u ∧ ∀ u', node v ⊂ node u' → (node u).card ≤ (node u').card
  then h.choose else r

variable {node : V → Finset α} {r : V}

lemma par_spec (h : Lam node r) (v : V) (hv : v ≠ r) :
    node v ⊂ node (par node r v) ∧
      ∀ u', node v ⊂ node u' → (node (par node r v)).card ≤ (node u').card := by
  have hex : ∃ u, v ≠ r ∧ node v ⊂ node u ∧
      ∀ u', node v ⊂ node u' → (node u).card ≤ (node u').card := by
    have hne : (univ.filter (fun u => node v ⊂ node u)).Nonempty :=
      ⟨r, by
        simp only [mem_filter, mem_univ, true_and]
        exact ssubset_of_subset_of_ne (h.top v) (fun he => hv (h.inj he))⟩
    obtain ⟨u, hu, hmin⟩ := exists_min_image _ (fun u => (node u).card) hne
    exact ⟨u, hv, by simpa using hu, fun u' hu' => hmin u' (by simpa using hu')⟩
  unfold par
  rw [dif_pos hex]
  exact ⟨hex.choose_spec.2.1, hex.choose_spec.2.2⟩

lemma par_root : par node r r = r := by
  unfold par
  rw [dif_neg]
  rintro ⟨u, h, _⟩
  exact h rfl

lemma par_ssub (h : Lam node r) {v : V} (hv : v ≠ r) : node v ⊂ node (par node r v) :=
  (par_spec h v hv).1

lemma sub_par (h : Lam node r) (v : V) : node v ⊆ node (par node r v) := by
  by_cases hv : v = r
  · subst hv; rw [par_root]
  · exact (par_ssub h hv).subset

lemma par_min (h : Lam node r) {v u : V} (hv : v ≠ r) (hu : node v ⊂ node u) :
    node (par node r v) ⊆ node u := by
  have hp := par_spec h v hv
  obtain ⟨a, ha⟩ := h.ne v
  rcases h.lam (par node r v) u with hd | hs | hs
  · exact absurd (hd (singleton_subset_iff.mpr (hp.1.subset ha))
      (singleton_subset_iff.mpr (hu.subset ha))) (by simp)
  · exact hs
  · have h1 := hp.2 u hu
    have := eq_of_subset_of_card_le hs h1
    rw [this]

lemma par_ne (h : Lam node r) {v : V} (hv : v ≠ r) : par node r v ≠ v := by
  intro he
  have := par_ssub h hv
  rw [he] at this
  exact lt_irrefl _ this

/-- The tree: `u ~ v` iff one is the parent of the other. -/
def G (node : V → Finset α) (r : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (v = par node r u ∨ u = par node r v)
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

lemma G_adj {u v : V} : (G node r).Adj u v ↔ u ≠ v ∧ (v = par node r u ∨ u = par node r v) :=
  Iff.rfl

lemma adj_par (h : Lam node r) {v : V} (hv : v ≠ r) : (G node r).Adj v (par node r v) :=
  G_adj.mpr ⟨(par_ne h hv).symm, Or.inl rfl⟩

lemma reach_root (h : Lam node r) : ∀ k, ∀ v, (node r).card - (node v).card ≤ k →
    (G node r).Reachable v r := by
  intro k
  induction k with
  | zero =>
    intro v hv
    have : node v = node r := eq_of_subset_of_card_le (h.top v) (by omega)
    rw [h.inj this]
  | succ k ih =>
    intro v hv
    by_cases hvr : v = r
    · subst hvr; rfl
    have hlt := card_lt_card (par_ssub h hvr)
    have hle := card_le_card (h.top (par node r v))
    exact (adj_par h hvr).reachable.trans (ih _ (by omega))

lemma connected (h : Lam node r) : (G node r).Connected := by
  have : Nonempty V := ⟨r⟩
  exact ⟨fun u v => (reach_root h _ u le_rfl).trans (reach_root h _ v le_rfl).symm⟩

lemma edge_inj (h : Lam node r) {u v : V} (hu : u ≠ r) (hv : v ≠ r)
    (he : s(u, par node r u) = s(v, par node r v)) : u = v := by
  rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have a1 := par_ssub h hu
    have a2 := par_ssub h hv
    rw [h2] at a1
    rw [← h1] at a2
    exact lt_asymm a1 a2

lemma mem_edgeSet_iff (h : Lam node r) (e : Sym2 V) :
    e ∈ (G node r).edgeSet ↔ ∃ v, v ≠ r ∧ e = s(v, par node r v) := by
  induction e with
  | _ a b =>
    rw [mem_edgeSet, G_adj]
    constructor
    · rintro ⟨hab, hb | ha⟩
      · refine ⟨a, ?_, by rw [hb]⟩
        rintro rfl
        rw [par_root] at hb
        exact hab hb.symm
      · refine ⟨b, ?_, by rw [ha, Sym2.eq_swap]⟩
        rintro rfl
        rw [par_root] at ha
        exact hab ha
    · rintro ⟨v, hv, he⟩
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact adj_par h hv
      · exact (adj_par h hv).symm

lemma edgeSet_eq (h : Lam node r) :
    (G node r).edgeSet = ↑((univ.erase r).image (fun v => s(v, par node r v))) := by
  ext e
  rw [mem_edgeSet_iff h]
  simp only [coe_image, coe_erase, coe_univ, Set.mem_image, Set.mem_sdiff, Set.mem_univ,
    Set.mem_singleton_iff, true_and]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩

lemma isTree (h : Lam node r) : (G node r).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨connected h, ?_⟩
  rw [edgeSet_eq h, Nat.card_coe_set_eq, Set.ncard_coe_finset, card_image_of_injOn,
    card_erase_of_mem (mem_univ r), Nat.card_eq_fintype_card, card_univ]
  · have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
    omega
  · intro u hu v hv he
    exact edge_inj h (by simpa using hu) (by simpa using hv) he

lemma reach_sub_aux (h : Lam node r) {a : V} (ha : a ≠ r) : ∀ u c
    (_ : ((G node r).deleteEdges {s(a, par node r a)}).Walk u c), node u ⊆ node a →
    node c ⊆ node a := by
  intro u c p
  induction p with
  | nil => exact id
  | @cons u w c hadj _ ih =>
    intro hu
    apply ih
    rw [deleteEdges_adj, G_adj] at hadj
    obtain ⟨⟨huw, hw | hu'⟩, hne⟩ := hadj
    · have hur : u ≠ r := by
        rintro rfl; rw [par_root] at hw; exact huw hw.symm
      have hua : u ≠ a := by
        rintro rfl; rw [hw] at hne; exact hne rfl
      have hss : node u ⊂ node a := ssubset_of_subset_of_ne hu (fun he => hua (h.inj he))
      rw [hw]; exact par_min h hur hss
    · rw [hu'] at hu
      exact (sub_par h w).trans hu

lemma reach_of_sub (h : Lam node r) {a : V} (ha : a ≠ r) : ∀ k c,
    (node a).card - (node c).card ≤ k → node c ⊆ node a →
    ((G node r).deleteEdges {s(a, par node r a)}).Reachable c a := by
  intro k
  induction k with
  | zero =>
    intro c hk hc
    have : node c = node a := eq_of_subset_of_card_le hc (by omega)
    rw [h.inj this]
  | succ k ih =>
    intro c hk hc
    by_cases hca : c = a
    · subst hca; rfl
    have hss : node c ⊂ node a := ssubset_of_subset_of_ne hc (fun he => hca (h.inj he))
    have hcr : c ≠ r := by
      rintro rfl
      exact absurd (hss.trans_le (h.top a)) (lt_irrefl _)
    have hpa := par_min h hcr hss
    have hlt := card_lt_card (par_ssub h hcr)
    have hle := card_le_card hpa
    have hadj : ((G node r).deleteEdges {s(a, par node r a)}).Adj c (par node r c) := by
      rw [deleteEdges_adj]
      refine ⟨adj_par h hcr, ?_⟩
      intro hmem
      rw [Set.mem_singleton_iff] at hmem
      exact hca (edge_inj h hcr ha hmem)
    exact hadj.reachable.trans (ih _ (by omega) hpa)

lemma reach_iff_sub (h : Lam node r) {a : V} (ha : a ≠ r) (c : V) :
    ((G node r).deleteEdges {s(a, par node r a)}).Reachable a c ↔ node c ⊆ node a := by
  constructor
  · rintro ⟨p⟩
    exact reach_sub_aux h ha a c p le_rfl
  · intro hc
    exact (reach_of_sub h ha _ c le_rfl hc).symm

lemma reach_x_iff (h : Lam node r) {a : V} (ha : a ≠ r) (ι : α → V)
    (hι : ∀ z ∈ node r, node (ι z) = {z}) {x : α} (hx : x ∈ node r) (hxa : x ∉ node a)
    {v : α} (hv : v ∈ node r) :
    ((G node r).deleteEdges {s(a, par node r a)}).Reachable (ι x) (ι v) ↔ v ∉ node a := by
  have hT := isTree h
  have key : ∀ z ∈ node r, ((G node r).deleteEdges {s(a, par node r a)}).Reachable a (ι z) ↔
      z ∈ node a := by
    intro z hz
    rw [reach_iff_sub h ha, hι z hz, singleton_subset_iff]
  have hxa' := (key x hx).not.mpr hxa
  have hxp : ((G node r).deleteEdges {s(a, par node r a)}).Reachable (ι x) (par node r a) := by
    rcases reach_or_reach hT.connected (a := a) (b := par node r a) (ι x) with h1 | h1
    · exact absurd h1.symm hxa'
    · exact h1
  constructor
  · intro hR hva
    exact hxa' (((key v hv).mpr hva).trans hR.symm)
  · intro hva
    have hva' := (key v hv).not.mpr hva
    rcases reach_or_reach hT.connected (a := a) (b := par node r a) (ι v) with h1 | h1
    · exact absurd h1.symm hva'
    · exact hxp.trans h1.symm

lemma exists_child (h : Lam node r) (u : V) : ∀ k c, (node u).card - (node c).card ≤ k →
    node c ⊂ node u → ∃ c', par node r c' = u ∧ c' ≠ u ∧ node c ⊆ node c' := by
  intro k
  induction k with
  | zero =>
    intro c hk hc
    exact absurd (card_lt_card hc) (by omega)
  | succ k ih =>
    intro c hk hc
    have hcr : c ≠ r := by
      rintro rfl
      exact absurd (hc.trans_le (h.top u)) (lt_irrefl _)
    by_cases hpc : par node r c = u
    · exact ⟨c, hpc, fun he => by rw [he] at hc; exact lt_irrefl _ hc, le_rfl⟩
    · have hpa := par_min h hcr hc
      have hss : node (par node r c) ⊂ node u :=
        ssubset_of_subset_of_ne hpa (fun he => hpc (h.inj he))
      have hlt := card_lt_card (par_ssub h hcr)
      obtain ⟨c', h1, h2, h3⟩ := ih _ (by omega) hss
      exact ⟨c', h1, h2, (sub_par h c).trans h3⟩

lemma leaf (h : Lam node r) (ι : α → V) (hι : ∀ z ∈ node r, node (ι z) = {z}) {x : α}
    (hx : x ∈ node r) (hxr : ∀ v, x ∈ node v → v = r ∨ node v = {x}) (u : V)
    (hleaf : ∀ b c, (G node r).Adj u b → (G node r).Adj u c → b = c) :
    ∃ z ∈ node r, ι z = u := by
  have child_adj : ∀ c', par node r c' = u → c' ≠ u → (G node r).Adj u c' :=
    fun c' h1 h2 => G_adj.mpr ⟨h2.symm, Or.inr h1.symm⟩
  have sing : ∀ z ∈ node u, node u = {z} → ∃ z ∈ node r, ι z = u := by
    intro z hz hu
    have hzr : z ∈ node r := h.top u hz
    refine ⟨z, hzr, h.inj ?_⟩
    rw [hι z hzr, hu]
  by_cases hur : u = r
  · subst hur
    by_cases hS : node u = {x}
    · exact sing x hx hS
    · have h1 : node (ι x) ⊂ node u := by
        rw [hι x hx]
        exact ssubset_of_subset_of_ne (singleton_subset_iff.mpr hx) (Ne.symm hS)
      obtain ⟨c1, p1, n1, s1⟩ := exists_child h u _ _ le_rfl h1
      have hb : ∃ b ∈ node u, b ≠ x := by
        by_contra hcon
        push Not at hcon
        exact hS (eq_singleton_iff_unique_mem.mpr ⟨hx, hcon⟩)
      obtain ⟨b, hb, hbx⟩ := hb
      have h2 : node (ι b) ⊂ node u := by
        rw [hι b hb]
        refine ssubset_of_subset_of_ne (singleton_subset_iff.mpr hb) ?_
        intro he
        rw [← he] at hx
        exact hbx (mem_singleton.mp hx).symm
      obtain ⟨c2, p2, n2, s2⟩ := exists_child h u _ _ le_rfl h2
      have heq := hleaf c1 c2 (child_adj c1 p1 n1) (child_adj c2 p2 n2)
      rw [hι x hx, singleton_subset_iff] at s1
      rw [hι b hb, singleton_subset_iff] at s2
      rcases hxr c1 s1 with h3 | h3
      · exact absurd h3 n1
      · rw [← heq, h3] at s2
        exact absurd (mem_singleton.mp s2) hbx
  · obtain ⟨z, hz⟩ := h.ne u
    by_cases hu : node u = {z}
    · exact sing z hz hu
    · have hzr : z ∈ node r := h.top u hz
      have h1 : node (ι z) ⊂ node u := by
        rw [hι z hzr]
        exact ssubset_of_subset_of_ne (singleton_subset_iff.mpr hz) (Ne.symm hu)
      obtain ⟨c1, p1, n1, s1⟩ := exists_child h u _ _ le_rfl h1
      have heq := hleaf _ _ (adj_par h hur) (child_adj c1 p1 n1)
      have a1 := par_ssub h hur
      rw [heq] at a1
      have a2 := sub_par h c1
      rw [p1] at a2
      exact absurd (a1.trans_le a2) (lt_irrefl _)

end Generic

section Concrete
variable {n : ℕ} {S : Finset (Fin n)} {y : Finset (Fin n) → ℝ}

/-- The nodes: `S`, the support sets of `y` and the singletons of `S`. -/
noncomputable def nodes (S : Finset (Fin n)) (y : Finset (Fin n) → ℝ) : Finset (Finset (Fin n)) :=
  insert S ((univ.filter (fun A => 0 < y A)) ∪ S.image (fun v => {v}))

noncomputable def nd (S : Finset (Fin n)) (y : Finset (Fin n) → ℝ) (i : Fin (nodes S y).card) :
    Finset (Fin n) :=
  ((nodes S y).equivFin.symm i).1

noncomputable def rt (S : Finset (Fin n)) (y : Finset (Fin n) → ℝ) : Fin (nodes S y).card :=
  (nodes S y).equivFin ⟨S, mem_insert_self _ _⟩

noncomputable def iota (S : Finset (Fin n)) (y : Finset (Fin n) → ℝ) (v : Fin n) :
    Fin (nodes S y).card :=
  if h : {v} ∈ nodes S y then (nodes S y).equivFin ⟨{v}, h⟩ else rt S y

lemma mem_nodes {A : Finset (Fin n)} :
    A ∈ nodes S y ↔ A = S ∨ 0 < y A ∨ ∃ v ∈ S, {v} = A := by
  simp [nodes]

lemma nd_equiv {A : Finset (Fin n)} (hA : A ∈ nodes S y) :
    nd S y ((nodes S y).equivFin ⟨A, hA⟩) = A := by
  simp [nd]

lemma nd_mem (i : Fin (nodes S y).card) : nd S y i ∈ nodes S y := ((nodes S y).equivFin.symm i).2

lemma nd_inj : Function.Injective (nd S y) := fun _ _ h =>
  (nodes S y).equivFin.symm.injective (Subtype.ext h)

lemma nd_rt : nd S y (rt S y) = S := nd_equiv _

lemma nd_iota {v : Fin n} (hv : v ∈ S) : nd S y (iota S y v) = {v} := by
  have h : {v} ∈ nodes S y := mem_nodes.mpr (Or.inr (Or.inr ⟨v, hv, rfl⟩))
  unfold iota
  rw [dif_pos h, nd_equiv]

variable {d : Fin n → Fin n → ℝ}

lemma supp (hy : IsDualFeasible d S y) {A : Finset (Fin n)} (hA : 0 < y A) :
    A ⊆ S ∧ A.Nonempty ∧ A ≠ S := by
  by_contra hc
  have := hy.2.1 A hc
  linarith

lemma node_sub (hy : IsDualFeasible d S y) {A : Finset (Fin n)} (hA : A ∈ nodes S y) : A ⊆ S := by
  rcases mem_nodes.mp hA with rfl | h | ⟨v, hv, rfl⟩
  · exact le_rfl
  · exact (supp hy h).1
  · exact singleton_subset_iff.mpr hv

lemma lam_pair (hy : IsDualFeasible d S y)
    (hlam : ∀ A B, 0 < y A → 0 < y B → Disjoint A B ∨ A ⊆ B ∨ B ⊆ A)
    {A B : Finset (Fin n)} (hA : A ∈ nodes S y) (hB : B ∈ nodes S y) :
    Disjoint A B ∨ A ⊆ B ∨ B ⊆ A := by
  rcases mem_nodes.mp hA with rfl | h | ⟨v, hv, rfl⟩
  · exact Or.inr (Or.inr (node_sub hy hB))
  · rcases mem_nodes.mp hB with rfl | h' | ⟨w, hw, rfl⟩
    · exact Or.inr (Or.inl (node_sub hy hA))
    · exact hlam A B h h'
    · by_cases hwA : w ∈ A
      · exact Or.inr (Or.inr (singleton_subset_iff.mpr hwA))
      · exact Or.inl (disjoint_singleton_right.mpr hwA)
  · by_cases hvB : v ∈ B
    · exact Or.inr (Or.inl (singleton_subset_iff.mpr hvB))
    · exact Or.inl (disjoint_singleton_left.mpr hvB)

lemma lamN (hy : IsDualFeasible d S y) {x : Fin n} (hx : x ∈ S)
    (hlam : ∀ A B, 0 < y A → 0 < y B → Disjoint A B ∨ A ⊆ B ∨ B ⊆ A) :
    Lam (nd S y) (rt S y) where
  inj := nd_inj
  top v := by rw [nd_rt]; exact node_sub hy (nd_mem v)
  ne v := by
    rcases mem_nodes.mp (nd_mem (S := S) (y := y) v) with h | h | ⟨w, _, h⟩
    · rw [h]; exact ⟨x, hx⟩
    · exact (supp hy h).2.1
    · rw [← h]; exact singleton_nonempty w
  lam u v := lam_pair hy hlam (nd_mem u) (nd_mem v)

lemma hxr {x : Fin n} (hxy : ∀ A, x ∈ A → y A = 0) (v : Fin (nodes S y).card)
    (hv : x ∈ nd S y v) : v = rt S y ∨ nd S y v = {x} := by
  rcases mem_nodes.mp (nd_mem (S := S) (y := y) v) with h | h | ⟨w, _, h⟩
  · left; apply nd_inj; rw [h, nd_rt]
  · rw [hxy _ hv] at h; exact absurd h (lt_irrefl 0)
  · right; rw [← h] at hv ⊢; rw [mem_singleton.mp hv]

noncomputable def wt (S : Finset (Fin n)) (y : Finset (Fin n) → ℝ)
    (e : Sym2 (Fin (nodes S y).card)) : ℝ :=
  ∑ v ∈ univ.erase (rt S y), if e = s(v, par (nd S y) (rt S y) v) then y (nd S y v) else 0

noncomputable def tree (hy : IsDualFeasible d S y) {x : Fin n} (hx : x ∈ S)
    (hxy : ∀ A, x ∈ A → y A = 0)
    (hlam : ∀ A B, 0 < y A → 0 < y B → Disjoint A B ∨ A ⊆ B ∨ B ⊆ A) : SteinerTree S where
  m := (nodes S y).card
  ι := iota S y
  inj := fun u hu v hv h => by
    have := congrArg (nd S y) h
    rw [nd_iota hu, nd_iota hv] at this
    exact singleton_injective this
  T := { G := G (nd S y) (rt S y), isTree := isTree (lamN hy hx hlam), w := wt S y,
         w_nonneg := fun _ _ => sum_nonneg (fun v _ => by
           split_ifs
           · exact hy.1 _
           · exact le_rfl) }
  leaves := fun a ha => by
    obtain ⟨z, hz, h⟩ := leaf (lamN hy hx hlam) (iota S y)
      (fun z hz => nd_iota (by rwa [nd_rt] at hz)) (by rw [nd_rt]; exact hx) (hxr hxy) a ha
    rw [nd_rt] at hz
    exact ⟨z, hz, h⟩

lemma wt_par (L : Lam (nd S y) (rt S y)) (v : Fin (nodes S y).card) (hv : v ≠ rt S y) :
    wt S y s(v, par (nd S y) (rt S y) v) = y (nd S y v) := by
  unfold wt
  rw [sum_eq_single v]
  · exact if_pos rfl
  · intro b hb hbv
    rw [if_neg]
    intro he
    exact hbv (edge_inj L (mem_erase.mp hb).1 hv he.symm)
  · intro hv'
    exact absurd (mem_erase.mpr ⟨hv, mem_univ v⟩) hv'

lemma main_aux (hd : DoublingMST.IsMetric d) {x : Fin n} (hx : x ∈ S)
    (hy : IsDualFeasible d S y) (hxy : ∀ A, x ∈ A → y A = 0) (F : SteinerTree S)
    (node : Fin F.m → Finset (Fin n)) (r : Fin F.m) (L : Lam node r) (hr : node r = S)
    (hG : F.T.G = G node r) (hw : ∀ v, v ≠ r → F.T.w s(v, par node r v) = y (node v))
    (hι : ∀ z ∈ S, node (F.ι z) = {z}) (hsurj : ∀ A, 0 < y A → ∃ v, node v = A) :
    Dominated d F ∧ F.weight = ∑ A, y A := by
  have hedges : F.edges = (univ.erase r).image (fun v => s(v, par node r v)) := by
    ext e
    rw [mem_edges_iff, hG, edgeSet_eq L, mem_coe]
    convert Iff.rfl
  have hside : ∀ v, v ≠ r → x ∉ node v → F.side s(v, par node r v) x = node v := by
    intro v hv hxv
    unfold SteinerTree.side
    rw [hG]
    ext z
    simp only [mem_filter]
    have hι' : ∀ z ∈ node r, node (F.ι z) = {z} := fun z hz => hι z (by rwa [hr] at hz)
    have hx' : x ∈ node r := by rw [hr]; exact hx
    constructor
    · rintro ⟨hz, hR⟩
      by_contra h
      exact hR ((reach_x_iff L hv F.ι hι' hx' hxv (by rw [hr]; exact hz)).mpr h)
    · intro hz
      have hzS : z ∈ S := by rw [← hr]; exact L.top v hz
      refine ⟨hzS, fun hR => ?_⟩
      exact (reach_x_iff L hv F.ι hι' hx' hxv (by rw [hr]; exact hzS)).mp hR hz
  have hdual : dualOf F x = y := by
    funext A
    unfold dualOf
    rw [hedges, sum_image (fun u hu v hv he =>
      edge_inj L (mem_erase.mp hu).1 (mem_erase.mp hv).1 he)]
    rw [sum_congr rfl (g := fun v => if node v = A then y (node v) else 0)]
    · by_cases hA : ∃ v ∈ univ.erase r, node v = A
      · obtain ⟨v, hv, hvA⟩ := hA
        rw [sum_eq_single v]
        · rw [if_pos hvA, hvA]
        · intro b _ hbv
          rw [if_neg]
          intro hb
          exact hbv (L.inj (hb.trans hvA.symm))
        · intro hv'; exact absurd hv hv'
      · rw [sum_eq_zero]
        · by_contra hne
          have pos := lt_of_le_of_ne (hy.1 A) hne
          obtain ⟨v, hvA⟩ := hsurj A pos
          by_cases hvr : v = r
          · rw [hvr, hr] at hvA
            exact (supp hy pos).2.2 hvA.symm
          · exact hA ⟨v, mem_erase.mpr ⟨hvr, mem_univ v⟩, hvA⟩
        · intro v hv
          rw [if_neg]
          intro hvA
          exact hA ⟨v, hv, hvA⟩
    · intro v hv
      have hvr := (mem_erase.mp hv).1
      by_cases hxv : x ∈ node v
      · simp only [hw v hvr, hxy _ hxv, ite_self]
      · rw [hside v hvr hxv, hw v hvr]
  refine ⟨(claim_4_1_sol d hd F x hx).mp (by rw [hdual]; exact hy), ?_⟩
  calc F.weight = ∑ A, dualOf F x A := by
        unfold dualOf SteinerTree.weight
        rw [sum_comm]
        apply sum_congr rfl
        intro e _
        rw [sum_ite_eq]
        simp
    _ = ∑ A, y A := by rw [hdual]

end Concrete

open scoped Classical in
theorem tree_of_laminar {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) (x : Fin n) (hx : x ∈ S)
    (y : Finset (Fin n) → ℝ) (hy : MetricTSPSublinear.IsDualFeasible d S y)
    (hxy : ∀ A, x ∈ A → y A = 0)
    (hlam : ∀ A B, 0 < y A → 0 < y B → Disjoint A B ∨ A ⊆ B ∨ B ⊆ A) :
    ∃ F : MetricTSPSublinear.SteinerTree S, MetricTSPSublinear.Dominated d F ∧
      F.weight = ∑ A, y A := by
  have L := lamN hy hx hlam
  refine ⟨tree hy hx hxy hlam, ?_⟩
  exact main_aux hd hx hy hxy (tree hy hx hxy hlam) (nd S y) (rt S y) L nd_rt rfl
    (fun v hv => wt_par L v hv) (fun z hz => nd_iota hz)
    (fun A hA => ⟨_, nd_equiv (mem_nodes.mpr (Or.inr (Or.inl hA)))⟩)

end MTSPLamTree



namespace MTSPLam

/-- support of `y` is laminar -/
def IsLaminar {n : ℕ} (y : Finset (Fin n) → ℝ) : Prop :=
  ∀ A B, 0 < y A → 0 < y B → Disjoint A B ∨ A ⊆ B ∨ B ⊆ A

open scoped Classical

/-- a valid cut of `S` -/
def Valid {n : ℕ} (S A : Finset (Fin n)) : Prop := A ⊆ S ∧ A.Nonempty ∧ A ≠ S

lemma valid_compl {n : ℕ} {S A : Finset (Fin n)} (h : A ⊆ S) :
    Valid S (S \ A) ↔ Valid S A := by
  unfold Valid
  constructor
  · rintro ⟨-, hne, hneS⟩
    refine ⟨h, ?_, ?_⟩
    · rw [Finset.nonempty_iff_ne_empty]; rintro rfl; simp at hneS
    · rintro rfl; simp at hne
  · rintro ⟨-, hne, hneS⟩
    refine ⟨Finset.sdiff_subset, ?_, ?_⟩
    · rw [Finset.sdiff_nonempty]; intro h'; exact hneS (Finset.Subset.antisymm h h')
    · intro h'
      obtain ⟨a, ha⟩ := hne
      have : a ∈ S \ A := by rw [h']; exact h ha
      simp [ha] at this

lemma transfer_sum {n : ℕ} (S : Finset (Fin n)) (x : Fin n) (hx : x ∈ S)
    (y : Finset (Fin n) → ℝ) (hy0 : ∀ A, ¬ Valid S A → y A = 0)
    (p : Finset (Fin n) → Prop) (hp : ∀ A, A ⊆ S → (p (S \ A) ↔ p A)) :
    ∑ A, (if p A then (if Valid S A ∧ x ∉ A then y A + y (S \ A) else 0) else 0)
      = ∑ A, (if p A then y A else 0) := by
  let φ : Finset (Fin n) → Finset (Fin n) := fun A => if A ⊆ S then S \ A else A
  have hφ : Function.Involutive φ := by
    intro A
    by_cases h : A ⊆ S
    · simp [φ, h, Finset.sdiff_sdiff_eq_self h]
    · simp [φ, h]
  have key : ∑ A, (if p A ∧ Valid S A ∧ x ∉ A then y (S \ A) else 0)
      = ∑ A, (if p A ∧ Valid S A ∧ x ∈ A then y A else 0) := by
    rw [← Equiv.sum_comp hφ.toPerm]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    simp only [Function.Involutive.coe_toPerm]
    by_cases hB : B ⊆ S
    · have e : φ B = S \ B := if_pos hB
      have hxB : x ∉ S \ B ↔ x ∈ B := by simp [hx]
      simp only [e, hp B hB, valid_compl hB, Finset.sdiff_sdiff_eq_self hB, hxB]
    · have e : φ B = B := if_neg hB
      simp only [e]
      have : ¬ Valid S B := fun h => hB h.1
      simp [this]
  rw [show (∑ A, (if p A then (if Valid S A ∧ x ∉ A then y A + y (S \ A) else 0) else 0)) =
      ∑ A, (if p A ∧ Valid S A ∧ x ∉ A then y A else 0) +
        ∑ A, (if p A ∧ Valid S A ∧ x ∉ A then y (S \ A) else 0) by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    by_cases hpA : p A <;> by_cases hV : Valid S A ∧ x ∉ A <;> simp [hpA, hV]]
  rw [key, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  by_cases hV : Valid S A
  · by_cases hxA : x ∈ A <;> by_cases hpA : p A <;> simp [hV, hxA, hpA]
  · simp [hV, hy0 A hV]

lemma sep_ineq {n : ℕ} (A B : Finset (Fin n)) (u v : Fin n) :
    (if ¬((u ∈ A ∪ B) ↔ (v ∈ A ∪ B)) then (1:ℝ) else 0)
      + (if ¬((u ∈ A ∩ B) ↔ (v ∈ A ∩ B)) then 1 else 0)
      ≤ (if ¬((u ∈ A) ↔ (v ∈ A)) then 1 else 0) + (if ¬((u ∈ B) ↔ (v ∈ B)) then 1 else 0) := by
  by_cases h1 : u ∈ A <;> by_cases h2 : u ∈ B <;> by_cases h3 : v ∈ A <;> by_cases h4 : v ∈ B <;>
    norm_num [h1, h2, h3, h4]

/-- weight of a cut -/
noncomputable def wt {n : ℕ} (S C : Finset (Fin n)) : ℝ := (C.card : ℝ) * ((S.card : ℝ) - C.card)

/-- potential -/
noncomputable def Phi {n : ℕ} (S : Finset (Fin n)) (z : Finset (Fin n) → ℝ) : ℝ :=
  ∑ C, z C * wt S C

lemma uncross_step {n : ℕ} (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) (x : Fin n) (hx : x ∈ S)
    (z : Finset (Fin n) → ℝ) (hz : MetricTSPSublinear.IsDualFeasible d S z)
    (hzx : ∀ A, x ∈ A → z A = 0) (A B : Finset (Fin n)) (hA : 0 < z A) (hB : 0 < z B)
    (hnot : ¬ (Disjoint A B ∨ A ⊆ B ∨ B ⊆ A)) :
    ∃ z', MetricTSPSublinear.IsDualFeasible d S z' ∧ ∑ C, z' C = ∑ C, z C ∧
      (∀ C, x ∈ C → z' C = 0) ∧ Phi S z' < Phi S z := by
  push Not at hnot
  obtain ⟨hdis, hAB, hBA⟩ := hnot
  obtain ⟨hz0, hzs, hzc⟩ := hz
  have vA : A ⊆ S ∧ A.Nonempty ∧ A ≠ S := by
    by_contra h; have := hzs A h; linarith
  have vB : B ⊆ S ∧ B.Nonempty ∧ B ≠ S := by
    by_contra h; have := hzs B h; linarith
  have xA : x ∉ A := fun h => by have := hzx A h; linarith
  have xB : x ∉ B := fun h => by have := hzx B h; linarith
  have xU : x ∉ A ∪ B := by simp [xA, xB]
  have xI : x ∉ A ∩ B := by simp [xA]
  have vU : A ∪ B ⊆ S ∧ (A ∪ B).Nonempty ∧ A ∪ B ≠ S :=
    ⟨Finset.union_subset vA.1 vB.1, vA.2.1.mono Finset.subset_union_left,
      fun h => xU (h ▸ hx)⟩
  have vI : A ∩ B ⊆ S ∧ (A ∩ B).Nonempty ∧ A ∩ B ≠ S :=
    ⟨Finset.inter_subset_left.trans vA.1, Finset.not_disjoint_iff_nonempty_inter.mp hdis,
      fun h => xI (h ▸ hx)⟩
  have n1 : A ≠ B := fun h => hAB (h ▸ subset_refl _)
  have n2 : A ≠ A ∪ B := fun h => hBA (Finset.union_eq_left.mp h.symm)
  have n3 : A ≠ A ∩ B := fun h => hAB (Finset.inter_eq_left.mp h.symm)
  have n4 : B ≠ A ∪ B := fun h => hAB (Finset.union_eq_right.mp h.symm)
  have n5 : B ≠ A ∩ B := fun h => hBA (Finset.inter_eq_right.mp h.symm)
  have n6 : A ∪ B ≠ A ∩ B := fun h => hAB (by
    intro a ha
    have : a ∈ A ∩ B := h ▸ Finset.mem_union_left B ha
    exact (Finset.mem_inter.mp this).2)
  set δ := min (z A) (z B) with hδdef
  have hδ : 0 < δ := lt_min hA hB
  have hδA : δ ≤ z A := min_le_left _ _
  have hδB : δ ≤ z B := min_le_right _ _
  let e : Finset (Fin n) → Finset (Fin n) → ℝ := fun D C => if C = D then 1 else 0
  let z' : Finset (Fin n) → ℝ :=
    fun C => z C + δ * (e (A ∪ B) C + e (A ∩ B) C - e A C - e B C)
  have z'A : z' A = z A - δ := by
    simp [z', e, n1, n2, n3]; ring
  have z'B : z' B = z B - δ := by
    simp [z', e, n1.symm, n4, n5]; ring
  have z'U : z' (A ∪ B) = z (A ∪ B) + δ := by
    simp [z', e, n2.symm, n4.symm, n6]
  have z'I : z' (A ∩ B) = z (A ∩ B) + δ := by
    simp [z', e, n3.symm, n5.symm, n6.symm]
  have z'o : ∀ C, C ≠ A → C ≠ B → C ≠ A ∪ B → C ≠ A ∩ B → z' C = z C := by
    intro C h1 h2 h3 h4
    simp [z', e, h1, h2, h3, h4]
  refine ⟨z', ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro C
    by_cases h1 : C = A
    · subst h1; rw [z'A]; linarith
    by_cases h2 : C = B
    · subst h2; rw [z'B]; linarith
    by_cases h3 : C = A ∪ B
    · subst h3; rw [z'U]; linarith [hz0 (A ∪ B)]
    by_cases h4 : C = A ∩ B
    · subst h4; rw [z'I]; linarith [hz0 (A ∩ B)]
    rw [z'o C h1 h2 h3 h4]; exact hz0 C
  · intro C hC
    have h1 : C ≠ A := by rintro rfl; exact hC vA
    have h2 : C ≠ B := by rintro rfl; exact hC vB
    have h3 : C ≠ A ∪ B := by rintro rfl; exact hC vU
    have h4 : C ≠ A ∩ B := by rintro rfl; exact hC vI
    rw [z'o C h1 h2 h3 h4]; exact hzs C hC
  · intro u hu v hv huv
    have h := hzc u hu v hv huv
    have hs := sep_ineq A B u v
    simp only [z', e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
    nlinarith
  · simp only [z', e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  · intro C hC
    have h1 : C ≠ A := by rintro rfl; exact xA hC
    have h2 : C ≠ B := by rintro rfl; exact xB hC
    have h3 : C ≠ A ∪ B := by rintro rfl; exact xU hC
    have h4 : C ≠ A ∩ B := by rintro rfl; exact xI hC
    rw [z'o C h1 h2 h3 h4]; exact hzx C hC
  · have hΦ : Phi S z' = Phi S z +
        δ * (wt S (A ∪ B) + wt S (A ∩ B) - wt S A - wt S B) := by
      unfold Phi
      have : ∀ C, z' C * wt S C = z C * wt S C + δ * ((e (A ∪ B) C * wt S C
          + e (A ∩ B) C * wt S C) - e A C * wt S C - e B C * wt S C) := fun C => by
        simp only [z']; ring
      simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, e,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hcard := Finset.card_union_add_card_inter A B
    have hia : (A ∩ B).card < A.card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, fun h => n3 h.symm⟩
    have hib : (A ∩ B).card < B.card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, fun h => n5 h.symm⟩
    have hcardR : ((A ∪ B).card : ℝ) = A.card + B.card - (A ∩ B).card := by
      have : ((A ∪ B).card : ℝ) + (A ∩ B).card = A.card + B.card := by exact_mod_cast hcard
      linarith
    have hiaR : ((A ∩ B).card : ℝ) < A.card := by exact_mod_cast hia
    have hibR : ((A ∩ B).card : ℝ) < B.card := by exact_mod_cast hib
    have hw : wt S (A ∪ B) + wt S (A ∩ B) - wt S A - wt S B < 0 := by
      unfold wt
      rw [hcardR]
      nlinarith [mul_pos (sub_pos.2 hiaR) (sub_pos.2 hibR)]
    rw [hΦ]
    nlinarith

theorem exists_laminar {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) (x : Fin n) (hx : x ∈ S)
    (y : Finset (Fin n) → ℝ) (hy : MetricTSPSublinear.IsDualFeasible d S y) :
    ∃ y' : Finset (Fin n) → ℝ, MetricTSPSublinear.IsDualFeasible d S y' ∧
      ∑ A, y' A = ∑ A, y A ∧ (∀ A, x ∈ A → y' A = 0) ∧ IsLaminar y' := by
  obtain ⟨hy0, hys, hyc⟩ := hy
  let y0 : Finset (Fin n) → ℝ := fun A => if Valid S A ∧ x ∉ A then y A + y (S \ A) else 0
  have hy0f : MetricTSPSublinear.IsDualFeasible d S y0 := by
    refine ⟨fun A => ?_, fun A hA => ?_, fun u hu v hv huv => ?_⟩
    · simp only [y0]; split_ifs
      · exact add_nonneg (hy0 _) (hy0 _)
      · exact le_refl _
    · have : ¬ Valid S A := hA
      simp [y0, this]
    · have h := hyc u hu v hv huv
      rw [Finset.sum_filter] at h ⊢
      have := transfer_sum S x hx y hys (fun A => ¬((u ∈ A) ↔ (v ∈ A))) (fun A _ => by
        simp only [Finset.mem_sdiff, hu, hv, true_and]; tauto)
      simp only [y0]
      refine (le_of_eq ?_).trans h
      convert this using 3
  have hy0sum : ∑ A, y0 A = ∑ A, y A := by
    have := transfer_sum S x hx y hys (fun _ => True) (fun _ _ => Iff.rfl)
    simpa using this
  have hy0x : ∀ A, x ∈ A → y0 A = 0 := fun A h => by simp [y0, h]
  let P : Set (Finset (Fin n) → ℝ) := {z | MetricTSPSublinear.IsDualFeasible d S z ∧
    ∑ A, z A = ∑ A, y A ∧ ∀ A, x ∈ A → z A = 0}
  have hPne : P.Nonempty := ⟨y0, hy0f, hy0sum, hy0x⟩
  have hPc : IsClosed P := by
    simp only [P, MetricTSPSublinear.IsDualFeasible, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (IsClosed.inter ?_ (IsClosed.inter ?_ ?_)) (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun A => isClosed_le continuous_const (continuous_apply A)
    · exact isClosed_iInter fun A => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply A) continuous_const
    · refine isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_iInter fun v =>
        isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_le ?_ continuous_const
      exact continuous_finsetSum _ fun A _ => continuous_apply A
    · exact isClosed_eq (continuous_finsetSum _ fun A _ => continuous_apply A) continuous_const
    · exact isClosed_iInter fun A => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply A) continuous_const
  have hPb : Bornology.IsBounded P := by
    refine (Metric.isBounded_Icc (0 : Finset (Fin n) → ℝ) (fun _ => ∑ A, y A)).subset ?_
    rintro z ⟨⟨hz0, -, -⟩, hzsum, -⟩
    refine ⟨fun A => hz0 A, fun A => ?_⟩
    rw [← hzsum]
    exact Finset.single_le_sum (fun B _ => hz0 B) (Finset.mem_univ A)
  have hPk : IsCompact P := Metric.isCompact_of_isClosed_isBounded hPc hPb
  have hΦc : Continuous (Phi S) :=
    continuous_finsetSum _ fun A _ => (continuous_apply A).mul continuous_const
  obtain ⟨z, ⟨hzf, hzsum, hzx⟩, hmin⟩ := hPk.exists_isMinOn hPne hΦc.continuousOn
  refine ⟨z, hzf, hzsum, hzx, ?_⟩
  intro A B hA hB
  by_contra hnot
  obtain ⟨z', hz'f, hz'sum, hz'x, hlt⟩ := uncross_step d S x hx z hzf hzx A B hA hB hnot
  have := hmin (show z' ∈ P from ⟨hz'f, hz'sum.trans hzsum, hz'x⟩)
  exact absurd this (not_le.mpr hlt)

end MTSPLam



namespace MTSPL42
open MetricTSPSublinear

theorem lemma_4_2_sol {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (y : Finset (Fin n) → ℝ) (hy : IsDualFeasible d S y) :
    ∃ F : SteinerTree S, Dominated d F ∧ F.weight = ∑ A, y A := by
  obtain ⟨x, hx⟩ := hS
  obtain ⟨y', hy', hsum, hxy, hlam⟩ := MTSPLam.exists_laminar d hd S x hx y hy
  obtain ⟨F, hF, hw⟩ := MTSPLamTree.tree_of_laminar d hd S x hx y' hy' hxy hlam
  exact ⟨F, hF, hw.trans hsum⟩

end MTSPL42



open scoped Classical
open MetricTSPSublinear

namespace MTSPDual

/-- LP strong duality for standard-form LPs indexed by arbitrary finite types. -/
theorem lp_sd {ι κ : Type*} [Fintype ι] [Fintype κ] (M : ι → κ → ℝ) (c : κ → ℝ) (g : ι → ℝ)
    (u0 : κ → ℝ) (hu0 : ∀ j, 0 ≤ u0 j) (hM : ∀ i, ∑ j, M i j * u0 j = g i)
    (hopt : ∀ u : κ → ℝ, (∀ j, 0 ≤ u j) → (∀ i, ∑ j, M i j * u j = g i) →
      ∑ j, c j * u0 j ≤ ∑ j, c j * u j) :
    ∃ p : ι → ℝ, (∀ j, ∑ i, M i j * p i ≤ c j) ∧ ∑ i, g i * p i = ∑ j, c j * u0 j := by
  set eι := Fintype.equivFin ι
  set eκ := Fintype.equivFin κ
  obtain ⟨p, hp1, hp2, -⟩ := Polyhedral.lp_strong_duality
    (Matrix.of fun a b => M (eι.symm a) (eκ.symm b)) (c ∘ eκ.symm) (g ∘ eι.symm) (u0 ∘ eκ.symm)
    (fun j => hu0 _) (by
      funext a
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Function.comp]
      rw [Equiv.sum_comp eκ.symm (fun j => M (eι.symm a) j * u0 j)]
      exact hM _) (by
      intro u hu hMu
      have := hopt (u ∘ eκ) (fun j => hu _) (by
        intro i
        have h := congrFun hMu (eι i)
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Function.comp,
          Equiv.symm_apply_apply] at h
        rw [← h, ← Equiv.sum_comp eκ.symm]
        simp)
      simp only [dotProduct, Function.comp]
      rw [Equiv.sum_comp eκ.symm (fun j => c j * u0 j)]
      rw [← Equiv.sum_comp eκ.symm (fun j => c j * (u ∘ eκ) j)] at this
      simpa using this)
  refine ⟨p ∘ eι, fun j => ?_, ?_⟩
  · have h := hp1 (eκ j)
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Function.comp,
      Equiv.symm_apply_apply] at h
    rw [← Equiv.sum_comp eι.symm]
    simpa using h
  · simp only [dotProduct, Function.comp] at hp2
    rw [Equiv.sum_comp eκ.symm (fun j => c j * u0 j)] at hp2
    rw [← hp2, ← Equiv.sum_comp eι.symm]
    simp

variable {n : ℕ}

/-- `A` is a cut of `S`: `∅ ≠ A ⊊ S`. -/
abbrev IsCut (S A : Finset (Fin n)) : Prop := A ⊆ S ∧ A.Nonempty ∧ A ≠ S

/-- The primal objective. -/
noncomputable def obj (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) (x : Sym2 (Fin n) → ℝ) : ℝ :=
  ∑ e ∈ pairsIn S, DoublingMST.edgeCost d e * x e

lemma mem_pairsIn {S : Finset (Fin n)} {u v : Fin n} :
    s(u, v) ∈ pairsIn S ↔ u ∈ S ∧ v ∈ S ∧ u ≠ v := by
  simp [pairsIn, Sym2.mk_isDiag_iff, and_assoc]

lemma mem_cutEdges {S A : Finset (Fin n)} (_hA : A ⊆ S) {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) :
    s(u, v) ∈ cutEdges S A ↔ ¬ (u ∈ A ↔ v ∈ A) := by
  simp only [cutEdges, Finset.mem_image, Finset.mem_product, Finset.mem_sdiff, Prod.exists,
    Sym2.eq_iff]
  constructor
  · rintro ⟨a, b, ⟨ha, -, hb⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> tauto
  · intro h
    by_cases huA : u ∈ A
    · exact ⟨u, v, ⟨huA, hv, by tauto⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, u, ⟨by tauto, hu, huA⟩, Or.inr ⟨rfl, rfl⟩⟩

lemma cutEdges_subset {S A : Finset (Fin n)} (hA : A ⊆ S) : cutEdges S A ⊆ pairsIn S := by
  intro e he
  simp only [cutEdges, Finset.mem_image, Finset.mem_product, Finset.mem_sdiff, Prod.exists] at he
  obtain ⟨a, b, ⟨ha, hb, hbA⟩, rfl⟩ := he
  rw [mem_pairsIn]
  exact ⟨hA ha, hb, fun h => hbA (h ▸ ha)⟩

lemma edgeCost_mk {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (u v : Fin n) :
    DoublingMST.edgeCost d s(u, v) = d u v := by
  simp [DoublingMST.edgeCost, hd.2.1 v u]

lemma metric_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (u v : Fin n) :
    0 ≤ d u v := by
  have h := hd.2.2 u v u
  rw [(hd.1 u u).2 rfl, hd.2.1 v u] at h
  linarith

lemma edgeCost_nonneg {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (e : Sym2 (Fin n)) :
    0 ≤ DoublingMST.edgeCost d e := by
  induction e using Sym2.ind with
  | h u v => rw [edgeCost_mk hd]; exact metric_nonneg hd u v

lemma edgeCost_pos {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) {S : Finset (Fin n)}
    {e : Sym2 (Fin n)} (he : e ∈ pairsIn S) : 0 < DoublingMST.edgeCost d e := by
  induction e using Sym2.ind with
  | h u v =>
    rw [mem_pairsIn] at he
    rw [edgeCost_mk hd]
    exact lt_of_le_of_ne (metric_nonneg hd u v) (fun h => he.2.2 ((hd.1 u v).1 h.symm))

lemma sum_cut_eq {S : Finset (Fin n)} {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S)
    (f : Finset (Fin n) → ℝ) (hf : ∀ A, ¬ IsCut S A → f A = 0) :
    ∑ A, (if IsCut S A ∧ s(u, v) ∈ cutEdges S A then f A else 0) =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => ¬ ((u ∈ A) ↔ (v ∈ A))), f A := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases hc : IsCut S A
  · simp only [mem_cutEdges hc.1 hu hv]; exact if_congr (and_iff_right hc) rfl rfl
  · simp [hc, hf A hc]

lemma weak {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (S : Finset (Fin n))
    (y : Finset (Fin n) → ℝ) (hy : IsDualFeasible d S y) (x : Sym2 (Fin n) → ℝ)
    (hx : IsCutFeasible S x) : ∑ A, y A ≤ obj d S x := by
  obtain ⟨hy0, hyc, hyd⟩ := hy
  obtain ⟨hx0, hxc⟩ := hx
  have hdual : ∀ e ∈ pairsIn S, ∑ A, (if IsCut S A ∧ e ∈ cutEdges S A then y A else 0) ≤
      DoublingMST.edgeCost d e := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [mem_pairsIn] at he
      rw [sum_cut_eq he.1 he.2.1 y hyc, edgeCost_mk hd]
      exact hyd u he.1 v he.2.1 he.2.2
  calc ∑ A, y A = ∑ A, (if IsCut S A then y A else 0) := Finset.sum_congr rfl fun A _ => by
          split_ifs with h
          · rfl
          · exact hyc A h
    _ ≤ ∑ A, (if IsCut S A then y A * ∑ e ∈ cutEdges S A, x e else 0) :=
          Finset.sum_le_sum fun A _ => by
          split_ifs with h
          · exact le_mul_of_one_le_right (hy0 A) (hxc A h.1 h.2.1 h.2.2)
          · exact le_rfl
    _ = ∑ A, ∑ e ∈ pairsIn S, (if IsCut S A ∧ e ∈ cutEdges S A then y A else 0) * x e :=
          Finset.sum_congr rfl fun A _ => by
          split_ifs with h
          · rw [Finset.mul_sum, ← Finset.sum_subset (cutEdges_subset h.1)
              (f := fun e => (if IsCut S A ∧ e ∈ cutEdges S A then y A else 0) * x e)]
            · exact Finset.sum_congr rfl fun e he => by simp [h, he]
            · intro e _ he; simp [he]
          · simp [h]
    _ = ∑ e ∈ pairsIn S, x e * ∑ A, (if IsCut S A ∧ e ∈ cutEdges S A then y A else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun A _ => mul_comm _ _
    _ ≤ obj d S x := by
          unfold obj
          refine Finset.sum_le_sum fun e he => ?_
          rw [mul_comm (DoublingMST.edgeCost d e)]
          exact mul_le_mul_of_nonneg_left (hdual e he) (hx0 e)

lemma one_feasible (S : Finset (Fin n)) : IsCutFeasible S (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun A hA hne hAS => ?_⟩
  have hS : (S \ A).Nonempty := Finset.sdiff_nonempty.mpr (fun h => hAS (subset_antisymm hA h))
  have : (cutEdges S A).Nonempty := ((hne.product hS).image _)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.one_le_cast]
  exact Finset.card_pos.mpr this

lemma restrict_feasible {S : Finset (Fin n)} {x : Sym2 (Fin n) → ℝ} (hx : IsCutFeasible S x) :
    IsCutFeasible S (fun e => if e ∈ pairsIn S then x e else 0) := by
  refine ⟨fun e => ?_, fun A hA hne hAS => ?_⟩
  · dsimp only
    split_ifs
    · exact hx.1 e
    · exact le_rfl
  · rw [Finset.sum_congr rfl fun e he => if_pos (cutEdges_subset hA he)]
    exact hx.2 A hA hne hAS

lemma obj_restrict (d : Fin n → Fin n → ℝ) (S : Finset (Fin n)) (x : Sym2 (Fin n) → ℝ) :
    obj d S (fun e => if e ∈ pairsIn S then x e else 0) = obj d S x := by
  unfold obj
  exact Finset.sum_congr rfl fun e he => by dsimp only; rw [if_pos he]

lemma exists_opt {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (S : Finset (Fin n)) :
    ∃ x, IsCutFeasible S x ∧ ∀ x', IsCutFeasible S x' → obj d S x ≤ obj d S x' := by
  set P := pairsIn S with hP
  set B := obj d S (fun _ => 1) with hB
  let b : Sym2 (Fin n) → ℝ := fun e => if e ∈ P then B / DoublingMST.edgeCost d e else 0
  let K : Set (Sym2 (Fin n) → ℝ) :=
    {x | IsCutFeasible S x ∧ obj d S x ≤ B ∧ ∀ e, e ∉ P → x e = 0}
  have hcont : Continuous (obj d S) := by unfold obj; fun_prop
  have hKc : IsClosed K := by
    have h1 : IsClosed {x : Sym2 (Fin n) → ℝ | ∀ e, 0 ≤ x e} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)
    have h2 : IsClosed {x : Sym2 (Fin n) → ℝ |
        ∀ A ⊆ S, A.Nonempty → A ≠ S → 1 ≤ ∑ e ∈ cutEdges S A, x e} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun A => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_le continuous_const (by fun_prop)
    have h3 : IsClosed {x | obj d S x ≤ B} := isClosed_le hcont continuous_const
    have h4 : IsClosed {x : Sym2 (Fin n) → ℝ | ∀ e, e ∉ P → x e = 0} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun e => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply e) continuous_const
    have : K = ({x : Sym2 (Fin n) → ℝ | ∀ e, 0 ≤ x e} ∩ {x : Sym2 (Fin n) → ℝ |
        ∀ A ⊆ S, A.Nonempty → A ≠ S → 1 ≤ ∑ e ∈ cutEdges S A, x e}) ∩
        ({x | obj d S x ≤ B} ∩ {x : Sym2 (Fin n) → ℝ | ∀ e, e ∉ P → x e = 0}) := by
      ext x; simp only [K, IsCutFeasible, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
    rw [this]
    exact (h1.inter h2).inter (h3.inter h4)
  have hsub : K ⊆ Set.pi Set.univ (fun e => Set.Icc 0 (b e)) := by
    intro x hx e _
    obtain ⟨⟨hx0, -⟩, hxB, hxP⟩ := hx
    refine ⟨hx0 e, ?_⟩
    simp only [b]
    split_ifs with he
    · rw [le_div_iff₀ (edgeCost_pos hd he), mul_comm]
      refine le_trans ?_ hxB
      exact Finset.single_le_sum (f := fun e => DoublingMST.edgeCost d e * x e)
        (fun e _ => mul_nonneg (edgeCost_nonneg hd e) (hx0 e)) he
    · exact (hxP e he).le
  have hKcomp : IsCompact K :=
    (isCompact_univ_pi fun e => isCompact_Icc).of_isClosed_subset hKc hsub
  have h1K : (fun e => if e ∈ P then (1 : ℝ) else 0) ∈ K := by
    refine ⟨restrict_feasible (one_feasible S), ?_, fun e he => if_neg he⟩
    rw [obj_restrict]
  obtain ⟨xs, hxsK, hmin⟩ := hKcomp.exists_isMinOn ⟨_, h1K⟩ hcont.continuousOn
  refine ⟨xs, hxsK.1, fun x' hx' => ?_⟩
  by_cases hle : obj d S x' ≤ B
  · have hmem : (fun e => if e ∈ P then x' e else 0) ∈ K := by
      refine ⟨restrict_feasible hx', ?_, fun e he => if_neg he⟩
      rw [obj_restrict]; exact hle
    have := isMinOn_iff.mp hmin _ hmem
    rwa [obj_restrict] at this
  · have := isMinOn_iff.mp hmin _ h1K
    rw [obj_restrict] at this
    linarith

lemma cutLP_eq_of_opt {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (S : Finset (Fin n))
    (x : Sym2 (Fin n) → ℝ) (hx : IsCutFeasible S x)
    (hopt : ∀ x', IsCutFeasible S x' → obj d S x ≤ obj d S x') : cutLP d S = obj d S x := by
  have hbdd : BddBelow {t : ℝ | ∃ x : Sym2 (Fin n) → ℝ, IsCutFeasible S x ∧
      t = ∑ e ∈ pairsIn S, DoublingMST.edgeCost d e * x e} :=
    ⟨0, by
      rintro t ⟨x, hx, rfl⟩
      exact Finset.sum_nonneg fun e _ => mul_nonneg (edgeCost_nonneg hd e) (hx.1 e)⟩
  apply le_antisymm
  · exact csInf_le hbdd ⟨x, hx, rfl⟩
  · refine le_csInf ⟨obj d S x, x, hx, rfl⟩ ?_
    rintro t ⟨x', hx', rfl⟩
    exact hopt x' hx'

theorem cutLP_attained {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) :
    ∃ x : Sym2 (Fin n) → ℝ, IsCutFeasible S x ∧
      ∑ e ∈ pairsIn S, DoublingMST.edgeCost d e * x e = cutLP d S := by
  obtain ⟨x, hx, hopt⟩ := exists_opt hd S
  exact ⟨x, hx, (cutLP_eq_of_opt hd S x hx hopt).symm⟩

theorem weak_duality {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) (y : Finset (Fin n) → ℝ) (hy : MetricTSPSublinear.IsDualFeasible d S y) :
    ∑ A, y A ≤ MetricTSPSublinear.cutLP d S := by
  obtain ⟨x, hx, hopt⟩ := exists_opt hd S
  rw [cutLP_eq_of_opt hd S x hx hopt]
  exact weak hd S y hy x hx

theorem strong_duality {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) :
    ∃ y : Finset (Fin n) → ℝ, MetricTSPSublinear.IsDualFeasible d S y ∧
      ∑ A, y A = MetricTSPSublinear.cutLP d S := by
  obtain ⟨xs, hxs, hopt⟩ := exists_opt hd S
  rw [cutLP_eq_of_opt hd S xs hxs hopt]
  let M : Finset (Fin n) → Sym2 (Fin n) ⊕ Finset (Fin n) → ℝ := fun A j =>
    Sum.elim (fun e => if IsCut S A ∧ e ∈ cutEdges S A then 1 else 0)
      (fun B => if A = B then (if IsCut S A then -1 else 0) else 0) j
  let c : Sym2 (Fin n) ⊕ Finset (Fin n) → ℝ :=
    Sum.elim (fun e => if e ∈ pairsIn S then DoublingMST.edgeCost d e else 0) (fun _ => 0)
  let g : Finset (Fin n) → ℝ := fun A => if IsCut S A then 1 else 0
  have hMsum : ∀ A (v : Sym2 (Fin n) ⊕ Finset (Fin n) → ℝ), ∑ j, M A j * v j =
      if IsCut S A then ∑ e ∈ cutEdges S A, v (Sum.inl e) - v (Sum.inr A) else 0 := by
    intro A v
    rw [Fintype.sum_sum_type]
    split_ifs with h
    · simp [M, sub_eq_add_neg, ite_mul]
      rw [if_pos h]
      simp only [and_iff_right h]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    · simp [M, h]
  have hcsum : ∀ v : Sym2 (Fin n) ⊕ Finset (Fin n) → ℝ,
      ∑ j, c j * v j = obj d S (fun e => v (Sum.inl e)) := by
    intro v
    rw [Fintype.sum_sum_type]
    simp [c, obj, ite_mul]
  let u0 : Sym2 (Fin n) ⊕ Finset (Fin n) → ℝ :=
    Sum.elim xs (fun A => if IsCut S A then ∑ e ∈ cutEdges S A, xs e - 1 else 0)
  obtain ⟨p, hp, hpv⟩ := lp_sd M c g u0
    (by
      rintro (e | A)
      · exact hxs.1 e
      · simp only [u0, Sum.elim_inr]
        split_ifs with h
        · linarith [hxs.2 A h.1 h.2.1 h.2.2]
        · exact le_rfl)
    (by
      intro A
      rw [hMsum]
      simp only [u0, Sum.elim_inl, Sum.elim_inr, g]
      split_ifs <;> ring)
    (by
      intro u hu hMu
      rw [hcsum, hcsum]
      refine hopt _ ⟨fun e => hu _, fun A hA hne hAS => ?_⟩
      have h := hMu A
      rw [hMsum] at h
      simp only [g, if_pos (show IsCut S A from ⟨hA, hne, hAS⟩)] at h
      linarith [hu (Sum.inr A)])
  let y : Finset (Fin n) → ℝ := fun A => if IsCut S A then p A else 0
  refine ⟨y, ⟨fun A => ?_, fun A hA => ?_, fun u hu v hv huv => ?_⟩, ?_⟩
  · simp only [y]
    split_ifs with h
    · have := hp (Sum.inr A)
      simp [M, c] at this
      rw [if_pos h] at this
      linarith
    · exact le_rfl
  · simp only [y]
    exact if_neg hA
  · rw [← sum_cut_eq hu hv y (fun A h => by simp only [y]; exact if_neg h)]
    have := hp (Sum.inl s(u, v))
    simp only [M, c, Sum.elim_inl, if_pos (mem_pairsIn.mpr ⟨hu, hv, huv⟩), edgeCost_mk hd]
      at this
    refine le_of_eq_of_le (Finset.sum_congr rfl fun A _ => ?_) this
    by_cases h : IsCut S A ∧ s(u, v) ∈ cutEdges S A
    · simp [y, h.1, h]
    · simp [h]
  · rw [show ∑ A, y A = ∑ A, g A * p A from
      Finset.sum_congr rfl fun A _ => by simp only [y, g]; split_ifs <;> ring, hpv, hcsum]
    rfl

end MTSPDual



namespace MTSPHelly
open SimpleGraph MetricTSPSublinear

section Graph
variable {V : Type*} {G : SimpleGraph V}

lemma reach_or_reach_aux {a b : V} : ∀ (w t : V) (_p : G.Walk w t), t = a →
    (G.deleteEdges {s(a, b)}).Reachable w a ∨ (G.deleteEdges {s(a, b)}).Reachable w b := by
  intro w t p
  induction p with
  | nil => intro h; subst h; exact Or.inl (Reachable.refl _)
  | @cons u u' _ h p ih =>
    intro ht
    have ih := ih ht
    by_cases he : s(u, u') = s(a, b)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (Reachable.refl _)
      · exact Or.inr (Reachable.refl _)
    · have hadj : (G.deleteEdges {s(a, b)}).Adj u u' := by
        rw [deleteEdges_adj]; exact ⟨h, by simpa using he⟩
      rcases ih with h1 | h1
      · exact Or.inl (hadj.reachable.trans h1)
      · exact Or.inr (hadj.reachable.trans h1)

lemma reach_or_reach (hconn : G.Connected) {a b : V} (w : V) :
    (G.deleteEdges {s(a, b)}).Reachable w a ∨ (G.deleteEdges {s(a, b)}).Reachable w b := by
  obtain ⟨p⟩ := hconn.preconnected w a
  exact reach_or_reach_aux w a p rfl

lemma not_reach_of_adj (hac : G.IsAcyclic) {a b : V} (hadj : G.Adj a b) :
    ¬ (G.deleteEdges {s(a, b)}).Reachable a b :=
  isAcyclic_iff_forall_adj_isBridge.mp hac hadj

/-- In a tree, an edge lies on the path between `u` and `v` iff deleting it separates them. -/
lemma mem_path_edges_iff (hT : G.IsTree) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (e : Sym2 V) : e ∈ p.edges ↔ ¬ (G.deleteEdges {e}).Reachable u v := by
  classical
  constructor
  · intro he hR
    obtain ⟨q⟩ := hR
    let q' := q.toPath
    have hq'p : (q'.val.mapLe (G.deleteEdges_le {e})).IsPath := q'.property.mapLe _
    have heq : q'.val.mapLe (G.deleteEdges_le {e}) = p := by
      have := (hT.existsUnique_path u v).unique hq'p hp
      exact this
    rw [← heq, Walk.edges_mapLe_eq_edges] at he
    have := q'.val.edges_subset_edgeSet he
    rw [edgeSet_deleteEdges] at this
    exact this.2 rfl
  · intro hR
    by_contra he
    exact hR ⟨p.toDeleteEdge e he⟩

end Graph

section Arith

lemma arith1 (α γ S : ℝ) (hα : 0 < α ∧ α < 1) (hγ : γ = 0 ∨ γ = 1) :
    min (α + (|0 - γ| + S)) ((1 - α) + (|1 - γ| + S)) = |γ - α| + S := by
  have h1 : |α| = α := abs_of_pos hα.1
  have h2 : |1 - α| = 1 - α := abs_of_pos (by linarith)
  rcases hγ with rfl | rfl <;> norm_num [h1, h2, abs_sub_comm 1 α] <;> linarith

lemma arith2 (α β γ δ S : ℝ) (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1) (hγ : γ = 0 ∨ γ = 1)
    (hδ : δ = 0 ∨ δ = 1) :
    min (min (α + (|0 - γ| + |δ - 0| + S) + β) (α + (|0 - γ| + |δ - 1| + S) + (1 - β)))
        (min ((1 - α) + (|1 - γ| + |δ - 0| + S) + β) ((1 - α) + (|1 - γ| + |δ - 1| + S) + (1 - β)))
      = |α - γ| + |δ - β| + S := by
  have h1 : |α| = α := abs_of_pos hα.1
  have h2 : |1 - α| = 1 - α := abs_of_pos (by linarith)
  have h3 : |β| = β := abs_of_pos hβ.1
  have h4 : |1 - β| = 1 - β := abs_of_pos (by linarith)
  rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;>
    norm_num [h1, h2, h3, h4, abs_sub_comm 1 α, abs_sub_comm α 1, abs_sub_comm 1 β, abs_sub_comm β 1] <;>
    simp only [min_def] <;> split_ifs <;> linarith

end Arith

section Between

/-- `t` lies between `x` and `y` (on the real line). -/
def Bt (x y t : ℝ) : Prop := |x - t| + |t - y| = |x - y|

lemma btw_iff {x y t : ℝ} : Bt x y t ↔ (x ≤ t ∧ t ≤ y) ∨ (y ≤ t ∧ t ≤ x) := by
  unfold Bt
  constructor
  · intro h
    rcases le_total x t with h1 | h1 <;> rcases le_total t y with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h
      rcases le_total x y with h3 | h3
      · rw [abs_of_nonpos (by linarith)] at h; exact Or.inl ⟨h1, by linarith⟩
      · rw [abs_of_nonneg (by linarith)] at h; exact Or.inr ⟨by linarith, by linarith⟩
    · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h
      rcases le_total x y with h3 | h3
      · rw [abs_of_nonpos (by linarith)] at h; exact Or.inl ⟨by linarith, by linarith⟩
      · rw [abs_of_nonneg (by linarith)] at h; exact Or.inr ⟨by linarith, h1⟩
    · exact Or.inr ⟨h2, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      ring

lemma btw_left (x y : ℝ) : Bt x y x := btw_iff.mpr (by rcases le_total x y with h | h <;> simp [h])
lemma btw_right (x y : ℝ) : Bt x y y := btw_iff.mpr (by rcases le_total x y with h | h <;> simp [h])
lemma btw_self (x : ℝ) : Bt x x x := btw_left x x
lemma btw_symm {x y t : ℝ} (h : Bt x y t) : Bt y x t := by
  rw [btw_iff] at *; tauto

lemma btw_trans {p q y x : ℝ} (h1 : Bt p q y) (h2 : Bt y q x) : Bt p q x := by
  rw [btw_iff] at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ <;>
    first | (left; constructor <;> linarith) | (right; constructor <;> linarith)

lemma btw_conv {a b p q r : ℝ} (h1 : Bt a b p) (h2 : Bt q r a) (h3 : Bt q r b) : Bt q r p := by
  rw [btw_iff] at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases h3 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases le_total q r with _ | _ <;>
    first | (left; constructor <;> linarith) | (right; constructor <;> linarith)

lemma btw_lift {c d q r t : ℝ} (h1 : Bt c d q) (h2 : Bt c r t) (h3 : Bt d r t) : Bt q r t := by
  rw [btw_iff] at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases h3 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases le_total q t with _ | _ <;>
    first | (left; constructor <;> linarith) | (right; constructor <;> linarith)

lemma btw_med3 (α β γ : ℝ) :
    (Bt α β α ∧ Bt β γ α ∧ Bt α γ α) ∨ (Bt α β β ∧ Bt β γ β ∧ Bt α γ β) ∨
      (Bt α β γ ∧ Bt β γ γ ∧ Bt α γ γ) := by
  simp only [btw_iff]
  rcases le_total α β with _ | _ <;> rcases le_total β γ with _ | _ <;>
    rcases le_total α γ with _ | _ <;>
    first
    | (left; refine ⟨?_, ?_, ?_⟩ <;>
        first | (left; constructor <;> linarith) | (right; constructor <;> linarith))
    | (right; left; refine ⟨?_, ?_, ?_⟩ <;>
        first | (left; constructor <;> linarith) | (right; constructor <;> linarith))
    | (right; right; refine ⟨?_, ?_, ?_⟩ <;>
        first | (left; constructor <;> linarith) | (right; constructor <;> linarith))

/-- For `0/1` values betweenness fails only if the two ends agree and the middle differs. -/
lemma btw_01 {x y t : ℝ} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (ht : t = 0 ∨ t = 1) :
    Bt x y t ↔ ¬ (x = y ∧ t ≠ x) := by
  rw [btw_iff]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num

end Between

section Sides
variable {m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.IsTree)

/-- The edges of `G`, as ordered pairs with the smaller end first. -/
noncomputable def Es : Finset (Fin m × Fin m) := by
  classical exact Finset.univ.filter (fun x => x.1 < x.2 ∧ G.Adj x.1 x.2)

lemma mem_Es {e : Fin m × Fin m} : e ∈ Es G ↔ e.1 < e.2 ∧ G.Adj e.1 e.2 := by
  classical simp [Es]

/-- The side of `v` with respect to the edge `e = (a, b)`: `0` on the side of `a`, `1` on the side of `b`. -/
noncomputable def sd (e : Fin m × Fin m) (v : Fin m) : ℝ := by
  classical exact if (G.deleteEdges {s(e.1, e.2)}).Reachable e.1 v then 0 else 1

lemma sd_01 (e : Fin m × Fin m) (v : Fin m) : sd G e v = 0 ∨ sd G e v = 1 := by
  unfold sd; split_ifs <;> simp

include hG in
lemma sd_eq_iff {e : Fin m × Fin m} (he : e ∈ Es G) (u v : Fin m) :
    sd G e u = sd G e v ↔ (G.deleteEdges {s(e.1, e.2)}).Reachable u v := by
  rw [mem_Es] at he
  have hab := not_reach_of_adj hG.isAcyclic he.2
  have hu := reach_or_reach hG.connected (a := e.1) (b := e.2) u
  have hv := reach_or_reach hG.connected (a := e.1) (b := e.2) v
  unfold sd
  set R := (G.deleteEdges {s(e.1, e.2)}).Reachable
  split_ifs with h1 h2 h2
  · simp only [true_iff]; exact h1.symm.trans h2
  · simp only [zero_ne_one, false_iff]; intro h; exact h2 (h1.trans h)
  · simp only [one_ne_zero, false_iff]; intro h; exact h1 (h2.trans h.symm)
  · simp only [true_iff]
    have hu' : R u e.2 := hu.resolve_left (fun h => h1 h.symm)
    have hv' : R v e.2 := hv.resolve_left (fun h => h2 h.symm)
    exact hu'.trans hv'.symm

lemma sd_fst {e : Fin m × Fin m} : sd G e e.1 = 0 := by
  unfold sd; simp

include hG in
lemma sd_snd {e : Fin m × Fin m} (he : e ∈ Es G) : sd G e e.2 = 1 := by
  rw [mem_Es] at he
  unfold sd; simp [not_reach_of_adj hG.isAcyclic he.2]

include hG in
lemma sd_adj {e : Fin m × Fin m} (he : e ∈ Es G) {a b : Fin m} (hab : G.Adj a b)
    (hne : s(a, b) ≠ s(e.1, e.2)) : sd G e a = sd G e b := by
  rw [sd_eq_iff G hG he]
  apply Adj.reachable
  rw [deleteEdges_adj]; exact ⟨hab, by simpa using hne⟩

lemma pair_ne_of_ne {e f : Fin m × Fin m} (he : e ∈ Es G) (hf : f ∈ Es G) (hne : f ≠ e) :
    s(f.1, f.2) ≠ s(e.1, e.2) := by
  rw [mem_Es] at he hf
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hne (Prod.ext h1 h2)
  · have h3 := hf.1; rw [h1, h2] at h3; exact absurd (lt_trans he.1 h3) (lt_irrefl _)

include hG in
/-- The key separation lemma: if `e` does not separate `q` and `r` but `f` does, then both ends of `f`
are on the side of `q` with respect to `e`. -/
lemma sep {e f : Fin m × Fin m} (he : e ∈ Es G) (hf : f ∈ Es G) {q r : Fin m}
    (h1 : sd G e q = sd G e r) (h2 : sd G f q ≠ sd G f r) :
    sd G e f.1 = sd G e q ∧ sd G e f.2 = sd G e q := by
  classical
  rw [sd_eq_iff G hG he] at h1
  obtain ⟨W⟩ := h1
  let W' : G.Walk q r := W.mapLe (G.deleteEdges_le _)
  by_cases hmem : s(f.1, f.2) ∈ W'.edges
  · have hs1 : f.1 ∈ W.support := by
      rw [← Walk.support_mapLe_eq_support (G.deleteEdges_le _)]
      exact W'.fst_mem_support_of_mem_edges hmem
    have hs2 : f.2 ∈ W.support := by
      rw [← Walk.support_mapLe_eq_support (G.deleteEdges_le _)]
      exact W'.snd_mem_support_of_mem_edges hmem
    obtain ⟨W1, _, _⟩ := Walk.mem_support_iff_exists_append.mp hs1
    obtain ⟨W2, _, _⟩ := Walk.mem_support_iff_exists_append.mp hs2
    exact ⟨((sd_eq_iff G hG he _ _).mpr ⟨W1⟩).symm, ((sd_eq_iff G hG he _ _).mpr ⟨W2⟩).symm⟩
  · exact absurd ((sd_eq_iff G hG hf _ _).mpr ⟨W'.toDeleteEdge _ hmem⟩) h2

lemma abs_sd_sub (e : Fin m × Fin m) (u v : Fin m) :
    |sd G e u - sd G e v| = if sd G e u = sd G e v then 0 else 1 := by
  rcases sd_01 G e u with h1 | h1 <;> rcases sd_01 G e v with h2 | h2 <;> simp [h1, h2]

include hG in
lemma dist_eq_sum (u v : Fin m) :
    (unitTree G hG).dist u v = ∑ e ∈ Es G, |sd G e u - sd G e v| := by
  classical
  let p : G.Walk u v := (unitTree G hG).path u v
  have hp : p.IsPath := ((unitTree G hG).isTree.existsUnique_path u v).exists.choose_spec
  have h1 : (unitTree G hG).dist u v = (p.length : ℝ) := by
    simp only [TreeCoverLB.WeightedTree.dist, KServer.walkWeight, unitTree, List.map_const',
      List.sum_replicate, Walk.length_darts, nsmul_eq_mul, mul_one]
    rfl
  rw [h1, ← Walk.length_edges]
  have h2 : ∀ e ∈ Es G, |sd G e u - sd G e v| =
      if s(e.1, e.2) ∈ p.edges then (1 : ℝ) else 0 := by
    intro e he
    have h3 := sd_eq_iff G hG he u v
    have h4 := mem_path_edges_iff hG p hp (s(e.1, e.2))
    rw [abs_sd_sub]
    by_cases h : sd G e u = sd G e v
    · rw [if_pos h, if_neg (by rw [h4, not_not]; exact h3.mp h)]
    · rw [if_neg h, if_pos (by rw [h4]; exact fun h' => h (h3.mpr h'))]
  rw [Finset.sum_congr rfl h2, Finset.sum_boole]
  have h3 : ((Es G).filter (fun e => s(e.1, e.2) ∈ p.edges)).image (fun e => s(e.1, e.2)) =
      p.edges.toFinset := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨e, ⟨_, he⟩, rfl⟩; exact he
    · intro hx
      have hxG : x ∈ G.edgeSet := p.edges_subset_edgeSet hx
      induction x using Sym2.ind with
      | h x y =>
        have hxy : G.Adj x y := hxG
        rcases lt_or_gt_of_ne hxy.ne with hlt | hlt
        · exact ⟨(x, y), ⟨(mem_Es G).mpr ⟨hlt, hxy⟩, hx⟩, rfl⟩
        · exact ⟨(y, x), ⟨(mem_Es G).mpr ⟨hlt, hxy.symm⟩, by simpa [Sym2.eq_swap] using hx⟩,
            Sym2.eq_swap⟩
  have h4 : ((Es G).filter (fun e => s(e.1, e.2) ∈ p.edges)).card = p.edges.toFinset.card := by
    rw [← h3, Finset.card_image_of_injOn]
    intro e he f hf hef
    by_contra hne
    exact pair_ne_of_ne G (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 (Ne.symm hne)
      hef.symm
  rw [h4, List.toFinset_card_of_nodup hp.isTrail.edges_nodup]

lemma sd_nonneg (e : Fin m × Fin m) (v : Fin m) : 0 ≤ sd G e v := by
  rcases sd_01 G e v with h | h <;> norm_num [h]

lemma sd_le_one (e : Fin m × Fin m) (v : Fin m) : sd G e v ≤ 1 := by
  rcases sd_01 G e v with h | h <;> norm_num [h]

/-- The (unit-weight) tree distance between vertices, as a sum over edges. -/
noncomputable def DD (u v : Fin m) : ℝ := ∑ e ∈ Es G, |sd G e u - sd G e v|

lemma unitTree_w (e : Sym2 (Fin m)) : (unitTree G hG).w e = 1 := rfl

lemma ud_vv (u v : Fin m) : unitDist G hG (.vtx u) (.vtx v) = DD G u v := by
  simp only [unitDist, rdist, dist_eq_sum G hG, DD]

lemma ud_vi (c a b : Fin m) (h1 h2 α hα) : unitDist G hG (.vtx c) (.inner a b h1 h2 α hα) =
    min (α + DD G a c) ((1 - α) + DD G b c) := by
  simp only [unitDist, rdist, dist_eq_sum G hG, DD, unitTree_w, mul_one]

lemma ud_iv (c a b : Fin m) (h1 h2 α hα) : unitDist G hG (.inner a b h1 h2 α hα) (.vtx c) =
    min (α + DD G a c) ((1 - α) + DD G b c) := by
  simp only [unitDist, rdist, dist_eq_sum G hG, DD, unitTree_w, mul_one]

lemma ud_ii (a b c d : Fin m) (h1 h2 α hα h3 h4 β hβ) :
    unitDist G hG (.inner a b h1 h2 α hα) (.inner c d h3 h4 β hβ) =
    if a = c ∧ b = d then |α - β| else min
        (min (α + DD G a c + β) (α + DD G a d + (1 - β)))
        (min ((1 - α) + DD G b c + β) ((1 - α) + DD G b d + (1 - β))) := by
  simp only [unitDist, rdist, dist_eq_sum G hG, DD, unitTree_w, mul_one]

/-- Coordinates of a point of `R(G)`: one coordinate per edge. -/
noncomputable def cr : RPoint G → Fin m × Fin m → ℝ
  | .vtx v, e => sd G e v
  | .inner a b _ _ α _, e => if e = (a, b) then α else sd G e a

lemma mem_Es_of {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) : (a, b) ∈ Es G :=
  (mem_Es G).mpr ⟨h2, h1⟩

include hG in
lemma sd_snd_eq {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) {e : Fin m × Fin m} (he : e ∈ Es G)
    (hne : e ≠ (a, b)) : sd G e b = sd G e a :=
  (sd_adj G hG he h1 (pair_ne_of_ne G he (mem_Es_of G h1 h2) (Ne.symm hne))).symm

lemma sum_split {e0 : Fin m × Fin m} (h0 : e0 ∈ Es G) (f : Fin m × Fin m → ℝ) :
    ∑ e ∈ Es G, f e = f e0 + ∑ e ∈ (Es G).erase e0, f e :=
  (Finset.add_sum_erase _ _ h0).symm

lemma sum_split2 {e0 e1 : Fin m × Fin m} (h0 : e0 ∈ Es G) (h1 : e1 ∈ Es G) (hne : e1 ≠ e0)
    (f : Fin m × Fin m → ℝ) :
    ∑ e ∈ Es G, f e = f e0 + f e1 + ∑ e ∈ ((Es G).erase e0).erase e1, f e := by
  rw [sum_split G h0, ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne, h1⟩), add_assoc]

lemma sd_fst' (a b : Fin m) : sd G (a, b) a = 0 := sd_fst G

include hG in
lemma sd_snd' {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) : sd G (a, b) b = 1 :=
  sd_snd G hG (mem_Es_of G h1 h2)

lemma cr_inner_self (a b : Fin m) (h1 h2 α hα) :
    cr G (.inner a b h1 h2 α hα) (a, b) = α := by simp [cr]

lemma cr_inner_ne (a b : Fin m) (h1 h2 α hα) {e : Fin m × Fin m} (hne : e ≠ (a, b)) :
    cr G (.inner a b h1 h2 α hα) e = sd G e a := by simp [cr, hne]

lemma cr_vtx (v : Fin m) (e : Fin m × Fin m) : cr G (.vtx v) e = sd G e v := rfl

include hG in
lemma vi_formula (c a b : Fin m) (h1 h2 α hα) :
    min (α + DD G a c) ((1 - α) + DD G b c) =
      ∑ e ∈ Es G, |cr G (.vtx c) e - cr G (.inner a b h1 h2 α hα) e| := by
  have h0 := mem_Es_of G h1 h2
  have hac : DD G a c = |0 - sd G (a, b) c| + ∑ e ∈ (Es G).erase (a, b), |sd G e a - sd G e c| := by
    unfold DD; rw [sum_split G h0, sd_fst']
  have hbc : DD G b c = |1 - sd G (a, b) c| + ∑ e ∈ (Es G).erase (a, b), |sd G e a - sd G e c| := by
    unfold DD; rw [sum_split G h0, sd_snd' G hG h1 h2]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [sd_snd_eq G hG h1 h2 (Finset.mem_of_mem_erase he) (Finset.ne_of_mem_erase he)]
  have hR : ∑ e ∈ Es G, |cr G (.vtx c) e - cr G (.inner a b h1 h2 α hα) e| =
      |sd G (a, b) c - α| + ∑ e ∈ (Es G).erase (a, b), |sd G e a - sd G e c| := by
    rw [sum_split G h0, cr_vtx, cr_inner_self]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [cr_vtx, cr_inner_ne G a b h1 h2 α hα (Finset.ne_of_mem_erase he), abs_sub_comm]
  rw [hac, hbc, hR]
  exact arith1 _ _ _ hα (sd_01 G _ _)

include hG in
lemma ii_formula (a b c d : Fin m) (h1 h2 α hα h3 h4 β hβ) (hne : ¬ (a = c ∧ b = d)) :
    min (min (α + DD G a c + β) (α + DD G a d + (1 - β)))
        (min ((1 - α) + DD G b c + β) ((1 - α) + DD G b d + (1 - β))) =
      ∑ e ∈ Es G, |cr G (.inner a b h1 h2 α hα) e - cr G (.inner c d h3 h4 β hβ) e| := by
  have h0 := mem_Es_of G h1 h2
  have h1' := mem_Es_of G h3 h4
  have hne' : (c, d) ≠ (a, b) := fun h => hne ⟨(Prod.ext_iff.mp h).1.symm, (Prod.ext_iff.mp h).2.symm⟩
  set R := ((Es G).erase (a, b)).erase (c, d)
  have hR1 : ∀ e ∈ R, e ≠ (a, b) := fun e he => Finset.ne_of_mem_erase (Finset.mem_of_mem_erase he)
  have hR2 : ∀ e ∈ R, e ≠ (c, d) := fun e he => Finset.ne_of_mem_erase he
  have hR3 : ∀ e ∈ R, e ∈ Es G := fun e he => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he)
  have hd0 : sd G (a, b) d = sd G (a, b) c := sd_snd_eq G hG h3 h4 h0 hne'.symm
  have hb1 : sd G (c, d) b = sd G (c, d) a := sd_snd_eq G hG h1 h2 h1' hne'
  set S := ∑ e ∈ R, |sd G e a - sd G e c|
  have hac : DD G a c = |0 - sd G (a, b) c| + |sd G (c, d) a - 0| + S := by
    unfold DD; rw [sum_split2 G h0 h1' hne', sd_fst', sd_fst']
  have had : DD G a d = |0 - sd G (a, b) c| + |sd G (c, d) a - 1| + S := by
    unfold DD; rw [sum_split2 G h0 h1' hne', sd_fst', sd_snd' G hG h3 h4, hd0]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [sd_snd_eq G hG h3 h4 (hR3 e he) (hR2 e he)]
  have hbc : DD G b c = |1 - sd G (a, b) c| + |sd G (c, d) a - 0| + S := by
    unfold DD; rw [sum_split2 G h0 h1' hne', sd_snd' G hG h1 h2, sd_fst', hb1]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [sd_snd_eq G hG h1 h2 (hR3 e he) (hR1 e he)]
  have hbd : DD G b d = |1 - sd G (a, b) c| + |sd G (c, d) a - 1| + S := by
    unfold DD; rw [sum_split2 G h0 h1' hne', sd_snd' G hG h1 h2, sd_snd' G hG h3 h4, hb1, hd0]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [sd_snd_eq G hG h1 h2 (hR3 e he) (hR1 e he), sd_snd_eq G hG h3 h4 (hR3 e he) (hR2 e he)]
  have hR : ∑ e ∈ Es G, |cr G (.inner a b h1 h2 α hα) e - cr G (.inner c d h3 h4 β hβ) e| =
      |α - sd G (a, b) c| + |sd G (c, d) a - β| + S := by
    rw [sum_split2 G h0 h1' hne', cr_inner_self, cr_inner_self, cr_inner_ne G c d h3 h4 β hβ hne'.symm,
      cr_inner_ne G a b h1 h2 α hα hne']
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [cr_inner_ne G a b h1 h2 α hα (hR1 e he), cr_inner_ne G c d h3 h4 β hβ (hR2 e he)]
  rw [hac, had, hbc, hbd, hR]
  exact arith2 _ _ _ _ _ hα hβ (sd_01 G _ _) (sd_01 G _ _)

include hG in
/-- **The coordinate formula**: `unitDist` is the `ℓ¹` distance of the edge coordinates. -/
theorem ud_eq (p q : RPoint G) : unitDist G hG p q = ∑ e ∈ Es G, |cr G p e - cr G q e| := by
  cases p with
  | vtx u =>
    cases q with
    | vtx v => rw [ud_vv]; rfl
    | inner a b h1 h2 α hα => rw [ud_vi, vi_formula G hG]
  | inner a b h1 h2 α hα =>
    cases q with
    | vtx c =>
      rw [ud_iv, vi_formula G hG c a b h1 h2 α hα]
      exact Finset.sum_congr rfl fun e _ => abs_sub_comm _ _
    | inner c d h3 h4 β hβ =>
      rw [ud_ii]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        rw [sum_split G (mem_Es_of G h1 h2), cr_inner_self, cr_inner_self]
        have : ∑ e ∈ (Es G).erase (a, b),
            |cr G (.inner a b h1 h2 α hα) e - cr G (.inner a b h3 h4 β hβ) e| = 0 := by
          refine Finset.sum_eq_zero fun e he => ?_
          rw [cr_inner_ne G a b h1 h2 α hα (Finset.ne_of_mem_erase he),
            cr_inner_ne G a b h3 h4 β hβ (Finset.ne_of_mem_erase he), sub_self, abs_zero]
        rw [this, add_zero]
      · exact ii_formula G hG a b c d h1 h2 α hα h3 h4 β hβ h

/-- `r` lies on the geodesic `[p, q]`, in coordinates. -/
def InSeg (p q r : RPoint G) : Prop := ∀ e ∈ Es G, Bt (cr G p e) (cr G q e) (cr G r e)

include hG in
theorem seg_iff (p q r : RPoint G) : r ∈ seg G hG p q ↔ InSeg G p q r := by
  show unitDist G hG p r + unitDist G hG r q = unitDist G hG p q ↔ _
  rw [ud_eq G hG, ud_eq G hG, ud_eq G hG, ← Finset.sum_add_distrib, eq_comm,
    Finset.sum_eq_sum_iff_of_le (fun e _ => abs_sub_le _ _ _)]
  exact ⟨fun h e he => (h e he).symm, fun h e he => (h e he).symm⟩

/-- `x` is a median of `p, q, r`. -/
def IsMed (p q r x : RPoint G) : Prop := InSeg G p q x ∧ InSeg G q r x ∧ InSeg G p r x

lemma inseg_left (p q : RPoint G) : InSeg G p q p := fun _ _ => btw_left _ _
lemma inseg_right (p q : RPoint G) : InSeg G p q q := fun _ _ => btw_right _ _
lemma inseg_symm {p q r : RPoint G} (h : InSeg G p q r) : InSeg G q p r :=
  fun e he => btw_symm (h e he)

lemma med_swap12 {p q r x : RPoint G} (h : IsMed G p q r x) : IsMed G q p r x :=
  ⟨inseg_symm G h.1, h.2.2, h.2.1⟩
lemma med_swap23 {p q r x : RPoint G} (h : IsMed G p q r x) : IsMed G p r q x :=
  ⟨h.2.2, inseg_symm G h.2.1, h.1⟩

lemma med_reduce {p q r y x : RPoint G} (h1 : InSeg G p q y) (h2 : InSeg G p r y)
    (h : IsMed G y q r x) : IsMed G p q r x :=
  ⟨fun e he => btw_trans (h1 e he) (h.1 e he), h.2.1,
    fun e he => btw_trans (h2 e he) (h.2.2 e he)⟩

lemma inseg_conv {a b p q r : RPoint G} (h1 : InSeg G a b p) (h2 : InSeg G q r a)
    (h3 : InSeg G q r b) : InSeg G q r p :=
  fun e he => btw_conv (h1 e he) (h2 e he) (h3 e he)

lemma inseg_lift {c d q r t : RPoint G} (h1 : InSeg G c d q) (h2 : InSeg G c r t)
    (h3 : InSeg G d r t) : InSeg G q r t :=
  fun e he => btw_lift (h1 e he) (h2 e he) (h3 e he)

/-! ### Vertex medians -/

include hG in
lemma improve {u v w x : Fin m} (_hx : InSeg G (.vtx u) (.vtx v) (.vtx x)) {e0 : Fin m × Fin m}
    (h0 : e0 ∈ Es G) (hwx : sd G e0 w ≠ sd G e0 x) (huv : sd G e0 u ≠ sd G e0 v) :
    ∃ y, InSeg G (.vtx u) (.vtx v) (.vtx y) ∧ DD G w y < DD G w x := by
  classical
  let y := if sd G e0 w = 0 then e0.1 else e0.2
  have hy0 : sd G e0 y = sd G e0 w := by
    rcases sd_01 G e0 w with h | h
    · simp only [y, h, if_true]; exact sd_fst G
    · simp only [y, h, if_neg one_ne_zero]; exact sd_snd G hG h0
  have hy : ∀ e ∈ Es G, ∀ z : Fin m, sd G e e0.1 = sd G e z → sd G e e0.2 = sd G e z →
      sd G e y = sd G e z := by
    intro e _ z h1 h2
    by_cases h : sd G e0 w = 0
    · simp only [y, h, if_true]; exact h1
    · simp only [y, h, if_false]; exact h2
  refine ⟨y, ?_, ?_⟩
  · intro e he
    rw [cr_vtx, cr_vtx, cr_vtx, btw_01 (sd_01 G _ _) (sd_01 G _ _) (sd_01 G _ _)]
    rintro ⟨h1, h2⟩
    obtain ⟨k1, k2⟩ := sep G hG he h0 h1 huv
    exact h2 (hy e he u k1 k2)
  · apply Finset.sum_lt_sum
    · intro e he
      by_cases h : sd G e w = sd G e x
      · obtain ⟨k1, k2⟩ := sep G hG he h0 h hwx
        rw [hy e he w k1 k2, sub_self, abs_zero]; exact abs_nonneg _
      · rw [abs_sd_sub G e w x, if_neg h, abs_sd_sub]; split_ifs <;> norm_num
    · refine ⟨e0, h0, ?_⟩
      rw [hy0, sub_self, abs_zero, abs_sd_sub, if_neg hwx]; norm_num

include hG in
theorem vmed (u v w : Fin m) : ∃ x, IsMed G (.vtx u) (.vtx v) (.vtx w) (.vtx x) := by
  classical
  let M := Finset.univ.filter (fun x : Fin m => InSeg G (.vtx u) (.vtx v) (.vtx x))
  have huM : u ∈ M := by simp [M, inseg_left]
  obtain ⟨x, hxM, hmin⟩ := M.exists_min_image (fun x => DD G w x) ⟨u, huM⟩
  have hx : InSeg G (.vtx u) (.vtx v) (.vtx x) := (Finset.mem_filter.mp hxM).2
  have key : ∀ e0 ∈ Es G, sd G e0 w ≠ sd G e0 x → sd G e0 u ≠ sd G e0 v → False := by
    intro e0 h0 h1 h2
    obtain ⟨y, hy, hlt⟩ := improve G hG hx h0 h1 h2
    exact absurd (hmin y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)) (not_le.mpr hlt)
  have hxe : ∀ e ∈ Es G, ¬ (sd G e u = sd G e v ∧ sd G e x ≠ sd G e u) := by
    intro e he
    have := hx e he
    rwa [cr_vtx, cr_vtx, cr_vtx, btw_01 (sd_01 G _ _) (sd_01 G _ _) (sd_01 G _ _)] at this
  refine ⟨x, ?_, ?_, ?_⟩
  · exact hx
  · intro e he
    rw [cr_vtx, cr_vtx, cr_vtx, btw_01 (sd_01 G _ _) (sd_01 G _ _) (sd_01 G _ _)]
    rintro ⟨h1, h2⟩
    refine key e he (by rw [← h1]; exact Ne.symm h2) (fun h3 => hxe e he ⟨h3, ?_⟩)
    rw [h3]; exact h2
  · intro e he
    rw [cr_vtx, cr_vtx, cr_vtx, btw_01 (sd_01 G _ _) (sd_01 G _ _) (sd_01 G _ _)]
    rintro ⟨h1, h2⟩
    exact key e he (by rw [← h1]; exact Ne.symm h2) (fun h3 => hxe e he ⟨h3, h2⟩)

/-! ### Medians of arbitrary points -/

/-- `q` lies on the closed edge `[a, b]`: all its coordinates away from `(a, b)` are those of `a`. -/
def OnEdge (a b : Fin m) (q : RPoint G) : Prop := ∀ e ∈ Es G, e ≠ (a, b) → cr G q e = sd G e a

lemma onEdge_inner (a b : Fin m) (h1 h2 α hα) : OnEdge G a b (.inner a b h1 h2 α hα) :=
  fun _ _ hne => cr_inner_ne G a b h1 h2 α hα hne

lemma onEdge_a (a b : Fin m) : OnEdge G a b (.vtx a) := fun _ _ _ => rfl

include hG in
lemma onEdge_b {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) : OnEdge G a b (.vtx b) :=
  fun _ he hne => sd_snd_eq G hG h1 h2 he hne

lemma line {a b : Fin m} {p q r : RPoint G} (hp : OnEdge G a b p) (hq : OnEdge G a b q)
    (hr : OnEdge G a b r) : ∃ x, IsMed G p q r x := by
  have hoff : ∀ e ∈ Es G, e ≠ (a, b) → ∀ x y z : RPoint G, OnEdge G a b x → OnEdge G a b y →
      OnEdge G a b z → Bt (cr G x e) (cr G y e) (cr G z e) := by
    intro e he hne x y z hx hy hz
    rw [hx e he hne, hy e he hne, hz e he hne]; exact btw_self _
  have mk : ∀ x, OnEdge G a b x → Bt (cr G p (a, b)) (cr G q (a, b)) (cr G x (a, b)) →
      Bt (cr G q (a, b)) (cr G r (a, b)) (cr G x (a, b)) →
      Bt (cr G p (a, b)) (cr G r (a, b)) (cr G x (a, b)) → IsMed G p q r x := by
    intro x hx k1 k2 k3
    refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_⟩ <;>
    · by_cases hne : e = (a, b)
      · subst hne; assumption
      · exact hoff e he hne _ _ _ (by assumption) (by assumption) hx
  rcases btw_med3 (cr G p (a, b)) (cr G q (a, b)) (cr G r (a, b)) with
    ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
  · exact ⟨p, mk p hp k1 k2 k3⟩
  · exact ⟨q, mk q hq k1 k2 k3⟩
  · exact ⟨r, mk r hr k1 k2 k3⟩

lemma classify (a b : Fin m) (q : RPoint G) :
    OnEdge G a b q ∨ cr G q (a, b) = 0 ∨ cr G q (a, b) = 1 := by
  cases q with
  | vtx v => exact Or.inr (sd_01 G _ _)
  | inner c d h3 h4 β hβ =>
    by_cases h : (a, b) = (c, d)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact Or.inl (onEdge_inner G a b h3 h4 β hβ)
    · right; rw [cr_inner_ne G c d h3 h4 β hβ h]; exact sd_01 G _ _

lemma toA {a b : Fin m} {p r : RPoint G} (hp : OnEdge G a b p) (hr : cr G r (a, b) = 0) :
    InSeg G p r (.vtx a) := by
  intro e he
  by_cases hne : e = (a, b)
  · subst hne; rw [cr_vtx, hr, sd_fst']; exact btw_right _ _
  · rw [cr_vtx, hp e he hne]; exact btw_left _ _

include hG in
lemma toB {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) {p r : RPoint G} (hp : OnEdge G a b p)
    (hr : cr G r (a, b) = 1) : InSeg G p r (.vtx b) := by
  intro e he
  by_cases hne : e = (a, b)
  · subst hne; rw [cr_vtx, hr, sd_snd' G hG h1 h2]; exact btw_right _ _
  · rw [cr_vtx, hp e he hne, sd_snd_eq G hG h1 h2 he hne]; exact btw_left _ _

include hG in
lemma ab_inner (a b : Fin m) (h1 h2 α hα) : InSeg G (.vtx a) (.vtx b) (.inner a b h1 h2 α hα) := by
  intro e he
  by_cases hne : e = (a, b)
  · subst hne
    rw [cr_vtx, cr_vtx, cr_inner_self, sd_fst', sd_snd' G hG h1 h2, btw_iff]
    exact Or.inl ⟨hα.1.le, hα.2.le⟩
  · rw [cr_vtx, cr_vtx, cr_inner_ne G a b h1 h2 α hα hne, sd_snd_eq G hG h1 h2 he hne]
    exact btw_self _

include hG in
lemma ends (q : RPoint G) : ∃ c d : Fin m, InSeg G (.vtx c) (.vtx d) q ∧
    ∀ e ∈ Es G, (cr G q e = 0 ∨ cr G q e = 1) → sd G e c = cr G q e ∧ sd G e d = cr G q e := by
  cases q with
  | vtx v => exact ⟨v, v, inseg_left G _ _, fun _ _ _ => ⟨rfl, rfl⟩⟩
  | inner c d h3 h4 β hβ =>
    refine ⟨c, d, ab_inner G hG c d h3 h4 β hβ, fun e he h01 => ?_⟩
    by_cases hne : e = (c, d)
    · subst hne; rw [cr_inner_self] at h01
      rcases h01 with h | h <;> linarith [hβ.1, hβ.2]
    · rw [cr_inner_ne G c d h3 h4 β hβ hne, sd_snd_eq G hG h3 h4 he hne]; exact ⟨rfl, rfl⟩

include hG in
lemma vsep {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) {u v : Fin m} (hu : sd G (a, b) u = 0)
    (hv : sd G (a, b) v = 1) :
    InSeg G (.vtx u) (.vtx v) (.vtx a) ∧ InSeg G (.vtx u) (.vtx v) (.vtx b) := by
  have h0 := mem_Es_of G h1 h2
  have huv : sd G (a, b) u ≠ sd G (a, b) v := by rw [hu, hv]; norm_num
  constructor <;>
  · intro e he
    rw [cr_vtx, cr_vtx, cr_vtx, btw_01 (sd_01 G _ _) (sd_01 G _ _) (sd_01 G _ _)]
    rintro ⟨k1, k2⟩
    obtain ⟨k3, k4⟩ := sep G hG he h0 k1 huv
    exact k2 (by assumption)

include hG in
lemma gsep {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) {q r : RPoint G} (hq : cr G q (a, b) = 0)
    (hr : cr G r (a, b) = 1) : InSeg G q r (.vtx a) ∧ InSeg G q r (.vtx b) := by
  have h0 := mem_Es_of G h1 h2
  obtain ⟨c1, d1, hq1, hq2⟩ := ends G hG q
  obtain ⟨c2, d2, hr1, hr2⟩ := ends G hG r
  obtain ⟨k1, k2⟩ := hq2 _ h0 (Or.inl hq)
  obtain ⟨k3, k4⟩ := hr2 _ h0 (Or.inr hr)
  rw [hq] at k1 k2; rw [hr] at k3 k4
  have hc := vsep G hG h1 h2 k1 k3
  have hd := vsep G hG h1 h2 k1 k4
  have hc' := vsep G hG h1 h2 k2 k3
  have hd' := vsep G hG h1 h2 k2 k4
  have L : ∀ t : RPoint G, InSeg G (.vtx c1) (.vtx c2) t → InSeg G (.vtx c1) (.vtx d2) t →
      InSeg G (.vtx d1) (.vtx c2) t → InSeg G (.vtx d1) (.vtx d2) t → InSeg G q r t := by
    intro t t1 t2 t3 t4
    apply inseg_lift G hq1
    · exact inseg_symm G (inseg_lift G hr1 (inseg_symm G t1) (inseg_symm G t2))
    · exact inseg_symm G (inseg_lift G hr1 (inseg_symm G t3) (inseg_symm G t4))
  exact ⟨L _ hc.1 hd.1 hc'.1 hd'.1, L _ hc.2 hd.2 hc'.2 hd'.2⟩

lemma core_onEdge {a b : Fin m} {p q r : RPoint G} (t : Fin m) (ht : OnEdge G a b (.vtx t))
    (hto : ∀ p', OnEdge G a b p' → InSeg G p' r (.vtx t)) (hp : OnEdge G a b p)
    (hq : OnEdge G a b q) : ∃ x, IsMed G p q r x := by
  obtain ⟨x, hx⟩ := line G hp hq ht
  refine ⟨x, med_swap23 G (med_swap12 G ?_)⟩
  exact med_reduce G (inseg_symm G (hto p hp)) (inseg_symm G (hto q hq))
    (med_swap12 G (med_swap23 G hx))

include hG in
lemma core {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (q r : RPoint G) (hA : ∃ x, IsMed G (.vtx a) q r x) (hB : ∃ x, IsMed G (.vtx b) q r x) :
    ∃ x, IsMed G (.inner a b h1 h2 α hα) q r x := by
  set p : RPoint G := .inner a b h1 h2 α hα
  have hp := onEdge_inner G a b h1 h2 α hα
  have hA' := onEdge_a G a b
  have hB' := onEdge_b G hG h1 h2
  have mid : ∀ q r : RPoint G, cr G q (a, b) = 0 → cr G r (a, b) = 1 → IsMed G p q r p := by
    intro q r hq hr
    obtain ⟨k1, k2⟩ := gsep G hG h1 h2 hq hr
    exact ⟨inseg_left G _ _, inseg_conv G (ab_inner G hG a b h1 h2 α hα) k1 k2, inseg_left G _ _⟩
  rcases classify G a b q with hq | hq | hq <;> rcases classify G a b r with hr | hr | hr
  · exact line G hp hq hr
  · exact core_onEdge G a hA' (fun p' hp' => toA G hp' hr) hp hq
  · exact core_onEdge G b hB' (fun p' hp' => toB G hG h1 h2 hp' hr) hp hq
  · obtain ⟨x, hx⟩ := core_onEdge G a hA' (fun p' hp' => toA G hp' hq) hp hr
    exact ⟨x, med_swap23 G hx⟩
  · obtain ⟨x, hx⟩ := hA
    exact ⟨x, med_reduce G (toA G hp hq) (toA G hp hr) hx⟩
  · exact ⟨p, mid q r hq hr⟩
  · obtain ⟨x, hx⟩ := core_onEdge G b hB' (fun p' hp' => toB G hG h1 h2 hp' hq) hp hr
    exact ⟨x, med_swap23 G hx⟩
  · exact ⟨p, med_swap23 G (mid r q hr hq)⟩
  · obtain ⟨x, hx⟩ := hB
    exact ⟨x, med_reduce G (toB G hG h1 h2 hp hq) (toB G hG h1 h2 hp hr) hx⟩

/-- Number of interior points. -/
def nI : RPoint G → ℕ
  | .vtx _ => 0
  | .inner .. => 1

include hG in
lemma med_aux : ∀ n : ℕ, ∀ p q r : RPoint G, nI G p + nI G q + nI G r ≤ n →
    ∃ x, IsMed G p q r x := by
  intro n
  induction n with
  | zero =>
    intro p q r h
    cases p with
    | inner => simp [nI] at h
    | vtx u =>
      cases q with
      | inner => simp [nI] at h
      | vtx v =>
        cases r with
        | inner => simp [nI] at h
        | vtx w => obtain ⟨x, hx⟩ := vmed G hG u v w; exact ⟨_, hx⟩
  | succ n ih =>
    intro p q r h
    cases p with
    | inner a b h1 h2 α hα =>
      exact core G hG h1 h2 α hα q r (ih _ _ _ (by simp [nI] at h ⊢; omega))
        (ih _ _ _ (by simp [nI] at h ⊢; omega))
    | vtx u =>
      cases q with
      | inner a b h1 h2 α hα =>
        obtain ⟨x, hx⟩ := core G hG h1 h2 α hα (.vtx u) r (ih _ _ _ (by simp [nI] at h ⊢; omega))
          (ih _ _ _ (by simp [nI] at h ⊢; omega))
        exact ⟨x, med_swap12 G hx⟩
      | vtx v =>
        cases r with
        | inner a b h1 h2 α hα =>
          obtain ⟨x, hx⟩ := core G hG h1 h2 α hα (.vtx u) (.vtx v)
            (ih _ _ _ (by simp [nI])) (ih _ _ _ (by simp [nI]))
          exact ⟨x, med_swap23 G (med_swap12 G hx)⟩
        | vtx w => obtain ⟨x, hx⟩ := vmed G hG u v w; exact ⟨_, hx⟩

include hG in
/-- **Medians in `R(G)`**: any three points have a point on all three pairwise geodesics. -/
theorem exists_median (a b c : RPoint G) :
    ∃ x, x ∈ seg G hG a b ∧ x ∈ seg G hG b c ∧ x ∈ seg G hG a c := by
  obtain ⟨x, h1, h2, h3⟩ := med_aux G hG 3 a b c (by cases a <;> cases b <;> cases c <;> simp [nI])
  exact ⟨x, (seg_iff G hG _ _ _).mpr h1, (seg_iff G hG _ _ _).mpr h2, (seg_iff G hG _ _ _).mpr h3⟩

/-! ### Helly property -/

/-- Geodesic convexity. -/
def Cvx (S : Set (RPoint G)) : Prop := ∀ p ∈ S, ∀ q ∈ S, seg G hG p q ⊆ S

lemma helly3 {A B C : Set (RPoint G)} (hA : Cvx G hG A) (hB : Cvx G hG B) (hC : Cvx G hG C)
    (hAB : (A ∩ B).Nonempty) (hBC : (B ∩ C).Nonempty) (hAC : (A ∩ C).Nonempty) :
    ∃ p, p ∈ A ∧ p ∈ B ∧ p ∈ C := by
  obtain ⟨a, haB, haC⟩ := hBC
  obtain ⟨b, hbA, hbC⟩ := hAC
  obtain ⟨c, hcA, hcB⟩ := hAB
  obtain ⟨x, h1, h2, h3⟩ := exists_median G hG a b c
  exact ⟨x, hA b hbA c hcA h2, hB a haB c hcB h3, hC a haC b hbC h1⟩

lemma hellyN : ∀ k : ℕ, ∀ X : Fin (k + 1) → Set (RPoint G), (∀ i, Cvx G hG (X i)) →
    (∀ i j, (X i ∩ X j).Nonempty) → ∃ p, ∀ i, p ∈ X i := by
  intro k
  induction k with
  | zero =>
    intro X _ hint
    obtain ⟨p, hp, _⟩ := hint 0 0
    exact ⟨p, fun i => by rw [Fin.fin_one_eq_zero i]; exact hp⟩
  | succ k ih =>
    intro X hX hint
    let Y : Fin (k + 1) → Set (RPoint G) := fun i => X i.castSucc ∩ X (Fin.last (k + 1))
    have hY : ∀ i, Cvx G hG (Y i) := fun i p hp q hq =>
      Set.subset_inter (hX _ p hp.1 q hq.1) (hX _ p hp.2 q hq.2)
    have hYint : ∀ i j, (Y i ∩ Y j).Nonempty := by
      intro i j
      obtain ⟨p, h1, h2, h3⟩ := helly3 G hG (hX i.castSucc) (hX j.castSucc) (hX (Fin.last _))
        (hint _ _) (hint _ _) (hint _ _)
      exact ⟨p, ⟨h1, h3⟩, ⟨h2, h3⟩⟩
    obtain ⟨p, hp⟩ := ih Y hY hYint
    refine ⟨p, fun i => ?_⟩
    induction i using Fin.lastCases with
    | last => exact (hp 0).2
    | cast i => exact (hp i).1

end Sides
end MTSPHelly



namespace MTSPWL1
open MetricTSPSublinear SimpleGraph MTSPHelly Finset

variable {m : ℕ} (T : TreeCoverLB.WeightedTree (Fin m))

/-- Weighted tree distance as a sum over separating edges. -/
lemma wdist_eq_sum (u v : Fin m) :
    T.dist u v = ∑ e ∈ Es T.G, T.w s(e.1, e.2) * |sd T.G e u - sd T.G e v| := by
  classical
  let p : T.G.Walk u v := T.path u v
  have hp : p.IsPath := (T.isTree.existsUnique_path u v).exists.choose_spec
  have h1 : T.dist u v = (p.edges.map T.w).sum := by
    unfold TreeCoverLB.WeightedTree.dist KServer.walkWeight
    rw [Walk.edges, List.map_map]
    rfl
  rw [h1, ← List.sum_toFinset _ hp.isTrail.edges_nodup]
  have h2 : ∀ e ∈ Es T.G, T.w s(e.1, e.2) * |sd T.G e u - sd T.G e v| =
      if s(e.1, e.2) ∈ p.edges then T.w s(e.1, e.2) else 0 := by
    intro e he
    have h3 := sd_eq_iff T.G T.isTree he u v
    have h4 := mem_path_edges_iff T.isTree p hp (s(e.1, e.2))
    rw [abs_sd_sub]
    by_cases h : sd T.G e u = sd T.G e v
    · rw [if_pos h, if_neg (by rw [h4, not_not]; exact h3.mp h)]; ring
    · rw [if_neg h, if_pos (by rw [h4]; exact fun h' => h (h3.mpr h'))]; ring
  rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]
  have h3 : ((Es T.G).filter (fun e => s(e.1, e.2) ∈ p.edges)).image (fun e => s(e.1, e.2)) =
      p.edges.toFinset := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨e, ⟨_, he⟩, rfl⟩; exact he
    · intro hx
      have hxG : x ∈ T.G.edgeSet := p.edges_subset_edgeSet hx
      induction x using Sym2.ind with
      | h x y =>
        have hxy : T.G.Adj x y := hxG
        rcases lt_or_gt_of_ne hxy.ne with hlt | hlt
        · exact ⟨(x, y), ⟨(mem_Es T.G).mpr ⟨hlt, hxy⟩, hx⟩, rfl⟩
        · exact ⟨(y, x), ⟨(mem_Es T.G).mpr ⟨hlt, hxy.symm⟩, by simpa [Sym2.eq_swap] using hx⟩,
            Sym2.eq_swap⟩
  rw [← h3, Finset.sum_image]
  intro e he f hf hef
  by_contra hne
  exact pair_ne_of_ne T.G (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 (Ne.symm hne)
    hef.symm

/-- The weighted `ℓ¹` distance of coordinates. -/
noncomputable def L (p q : RPoint T.G) : ℝ :=
  ∑ e ∈ Es T.G, T.w s(e.1, e.2) * |cr T.G p e - cr T.G q e|

lemma w_nn {e : Fin m × Fin m} (he : e ∈ Es T.G) : 0 ≤ T.w s(e.1, e.2) :=
  T.w_nonneg _ ((mem_Es T.G).mp he).2

lemma L_tri (p q r : RPoint T.G) : L T p r ≤ L T p q + L T q r := by
  unfold L
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e he
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) (w_nn T he)

lemma L_comm (p q : RPoint T.G) : L T p q = L T q p := by
  unfold L; apply Finset.sum_congr rfl; intro e _; rw [abs_sub_comm]

lemma L_vv (u v : Fin m) : L T (.vtx u) (.vtx v) = T.dist u v := by
  rw [wdist_eq_sum]; rfl

lemma L_iv_a (a b : Fin m) (h1 h2 α hα) :
    L T (.inner a b h1 h2 α hα) (.vtx a) = α * T.w s(a, b) := by
  classical
  unfold L
  rw [Finset.sum_eq_single (a, b)]
  · simp only [cr, ite_true, if_true, sd_fst' T.G a b, sub_zero, abs_of_pos hα.1]; ring
  · intro e _ hne
    simp only [cr, if_neg hne, sub_self, abs_zero, mul_zero]
  · intro h; exact absurd (mem_Es_of T.G h1 h2) h

lemma L_iv_b (a b : Fin m) (h1 h2 α hα) :
    L T (.inner a b h1 h2 α hα) (.vtx b) = (1 - α) * T.w s(a, b) := by
  classical
  unfold L
  rw [Finset.sum_eq_single (a, b)]
  · simp only [cr, ite_true, if_true, sd_snd' T.G T.isTree h1 h2]
    rw [abs_of_neg (by linarith [hα.2])]; ring
  · intro e he hne
    simp only [cr, if_neg hne, sd_snd_eq T.G T.isTree h1 h2 he hne, sub_self, abs_zero, mul_zero]
  · intro h; exact absurd (mem_Es_of T.G h1 h2) h

lemma L_ii_same (a b : Fin m) (h1 h2 α hα h3 h4 β hβ) :
    L T (.inner a b h1 h2 α hα) (.inner a b h3 h4 β hβ) = |α - β| * T.w s(a, b) := by
  classical
  unfold L
  rw [Finset.sum_eq_single (a, b)]
  · simp only [cr, ite_true, if_true]; ring
  · intro e _ hne
    simp only [cr, if_neg hne, sub_self, abs_zero, mul_zero]
  · intro h; exact absurd (mem_Es_of T.G h1 h2) h

lemma L_bound (p q : RPoint T.G) (x y : Fin m) (Lx Ly : ℝ) (hx : L T p (.vtx x) = Lx)
    (hy : L T q (.vtx y) = Ly) : L T p q ≤ Lx + T.dist x y + Ly :=
  calc L T p q ≤ L T p (.vtx x) + L T (.vtx x) q := L_tri T _ _ _
    _ ≤ L T p (.vtx x) + (L T (.vtx x) (.vtx y) + L T (.vtx y) q) :=
        by have := L_tri T (.vtx x) (.vtx y) q; linarith
    _ = Lx + T.dist x y + Ly := by rw [hx, L_vv, L_comm T (.vtx y) q, hy]; ring

/-- The tree distance of `R(T)` dominates the weighted `ℓ¹` distance of coordinates. -/
theorem L_le_rdist (p q : RPoint T.G) : L T p q ≤ rdist T p q := by
  cases p with
  | vtx u =>
    cases q with
    | vtx v => rw [L_vv]; rfl
    | inner a b h1 h2 α hα =>
      show _ ≤ min (α * T.w s(a, b) + T.dist a u) ((1 - α) * T.w s(a, b) + T.dist b u)
      apply le_min
      · have h := L_tri T (.vtx u) (.vtx a) (.inner a b h1 h2 α hα)
        rw [L_comm T (.vtx a), L_iv_a] at h
        have hs : L T (.vtx u) (.vtx a) = T.dist a u := by rw [L_comm, L_vv]
        rw [hs] at h; linarith
      · have h := L_tri T (.vtx u) (.vtx b) (.inner a b h1 h2 α hα)
        rw [L_comm T (.vtx b), L_iv_b] at h
        have hs : L T (.vtx u) (.vtx b) = T.dist b u := by rw [L_comm, L_vv]
        rw [hs] at h; linarith
  | inner a b h1 h2 α hα =>
    cases q with
    | vtx c =>
      show _ ≤ min (α * T.w s(a, b) + T.dist a c) ((1 - α) * T.w s(a, b) + T.dist b c)
      apply le_min
      · have := L_tri T (.inner a b h1 h2 α hα) (.vtx a) (.vtx c)
        rw [L_iv_a, L_vv] at this; linarith
      · have := L_tri T (.inner a b h1 h2 α hα) (.vtx b) (.vtx c)
        rw [L_iv_b, L_vv] at this; linarith
    | inner c d h3 h4 β hβ =>
      show _ ≤ (if a = c ∧ b = d then |α - β| * T.w s(a, b) else min
        (min (α * T.w s(a, b) + T.dist a c + β * T.w s(c, d))
             (α * T.w s(a, b) + T.dist a d + (1 - β) * T.w s(c, d)))
        (min ((1 - α) * T.w s(a, b) + T.dist b c + β * T.w s(c, d))
             ((1 - α) * T.w s(a, b) + T.dist b d + (1 - β) * T.w s(c, d))))
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        rw [L_ii_same]
      · have k := fun (x y : Fin m) (Lx Ly : ℝ) hx hy => L_bound T (.inner a b h1 h2 α hα) (.inner c d h3 h4 β hβ) x y Lx Ly hx hy
        have k1 := k a c _ _ (L_iv_a T a b h1 h2 α hα) (L_iv_a T c d h3 h4 β hβ)
        have k2 := k a d _ _ (L_iv_a T a b h1 h2 α hα) (L_iv_b T c d h3 h4 β hβ)
        have k3 := k b c _ _ (L_iv_b T a b h1 h2 α hα) (L_iv_a T c d h3 h4 β hβ)
        have k4 := k b d _ _ (L_iv_b T a b h1 h2 α hα) (L_iv_b T c d h3 h4 β hβ)
        refine le_min (le_min ?_ ?_) (le_min ?_ ?_) <;> linarith

lemma cr_mem (p : RPoint T.G) (e : Fin m × Fin m) : 0 ≤ cr T.G p e ∧ cr T.G p e ≤ 1 := by
  cases p with
  | vtx v => exact ⟨sd_nonneg T.G e v, sd_le_one T.G e v⟩
  | inner a b h1 h2 α hα =>
    simp only [cr]
    split_ifs
    · exact ⟨hα.1.le, hα.2.le⟩
    · exact ⟨sd_nonneg T.G e a, sd_le_one T.G e a⟩

end MTSPWL1



namespace MTSPLayer
open Finset

/-- The next element of `D` strictly above `v`, or `v` if none. -/
noncomputable def nxt (D : Finset ℝ) (v : ℝ) : ℝ :=
  if h : (D.filter (fun d' => v < d')).Nonempty then (D.filter (fun d' => v < d')).min' h else v

lemma le_nxt (D : Finset ℝ) (v : ℝ) : v ≤ nxt D v := by
  unfold nxt
  split_ifs with h
  · exact le_of_lt (Finset.mem_filter.mp (Finset.min'_mem _ h)).2
  · exact le_refl v

lemma nxt_le (D : Finset ℝ) (v w : ℝ) (hw : w ∈ D) (hvw : v < w) : nxt D v ≤ w := by
  unfold nxt
  rw [dif_pos ⟨w, Finset.mem_filter.mpr ⟨hw, hvw⟩⟩]
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hw, hvw⟩)

/-- Telescoping of gaps between two elements of `D`. -/
lemma tele (D : Finset ℝ) : ∀ (N : ℕ) (a b : ℝ), a ∈ D → b ∈ D → a ≤ b →
    (D.filter (fun t => a ≤ t ∧ t < b)).card ≤ N →
    ∑ t ∈ D.filter (fun t => a ≤ t ∧ t < b), (nxt D t - t) = b - a := by
  intro N
  induction N with
  | zero =>
    intro a b ha hb hab hc
    have he : D.filter (fun t => a ≤ t ∧ t < b) = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [he, Finset.sum_empty]
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]; ring
    · exfalso
      have : a ∈ D.filter (fun t => a ≤ t ∧ t < b) := Finset.mem_filter.mpr ⟨ha, le_refl a, h⟩
      rw [he] at this; simp at this
  | succ N ih =>
    intro a b ha hb hab hc
    rcases eq_or_lt_of_le hab with h | h
    · subst h
      have he : D.filter (fun t => a ≤ t ∧ t < a) = ∅ := by
        apply Finset.filter_false_of_mem; intro t _ ht; linarith [ht.1, ht.2]
      rw [he]; simp
    · set M := (D.filter (fun t => a ≤ t ∧ t < b)).max'
        ⟨a, Finset.mem_filter.mpr ⟨ha, le_refl a, h⟩⟩ with hM
      have hMmem := Finset.max'_mem (D.filter (fun t => a ≤ t ∧ t < b))
        ⟨a, Finset.mem_filter.mpr ⟨ha, le_refl a, h⟩⟩
      rw [← hM, Finset.mem_filter] at hMmem
      obtain ⟨hMD, haM, hMb⟩ := hMmem
      have hnext : nxt D M = b := by
        apply le_antisymm (nxt_le D M b hb hMb)
        unfold nxt
        rw [dif_pos ⟨b, Finset.mem_filter.mpr ⟨hb, hMb⟩⟩]
        apply Finset.le_min'
        intro y hy
        rw [Finset.mem_filter] at hy
        by_contra hyb
        push_neg at hyb
        have : y ≤ M := Finset.le_max' _ y (Finset.mem_filter.mpr ⟨hy.1, by linarith [hy.2], hyb⟩)
        linarith [hy.2]
      have hins : D.filter (fun t => a ≤ t ∧ t < b) =
          insert M (D.filter (fun t => a ≤ t ∧ t < M)) := by
        ext t
        simp only [Finset.mem_insert, Finset.mem_filter]
        constructor
        · rintro ⟨htD, hat, htb⟩
          by_cases htM : t = M
          · exact Or.inl htM
          · right
            refine ⟨htD, hat, lt_of_le_of_ne ?_ htM⟩
            exact Finset.le_max' _ t (Finset.mem_filter.mpr ⟨htD, hat, htb⟩)
        · rintro (rfl | ⟨htD, hat, htM⟩)
          · exact ⟨hMD, haM, hMb⟩
          · exact ⟨htD, hat, lt_trans htM hMb⟩
      have hnot : M ∉ D.filter (fun t => a ≤ t ∧ t < M) := by
        intro hh; exact lt_irrefl M (Finset.mem_filter.mp hh).2.2
      have hc' : (D.filter (fun t => a ≤ t ∧ t < M)).card ≤ N := by
        have := hc; rw [hins, Finset.card_insert_of_notMem hnot] at this; omega
      rw [hins, Finset.sum_insert hnot, ih a M ha hMD haM hc', hnext]
      ring

lemma tele' (D : Finset ℝ) (a b : ℝ) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≤ b) :
    ∑ t ∈ D.filter (fun t => a ≤ t ∧ t < b), (nxt D t - t) = b - a :=
  tele D _ a b ha hb hab le_rfl

/-- Layer-cake with a cap `ρ ∈ D`. -/
lemma tele_cap (D : Finset ℝ) (a b ρ : ℝ) (ha : a ∈ D) (hb : b ∈ D) (hρ : ρ ∈ D) (hab : a ≤ b) :
    ∑ t ∈ D.filter (fun t => a ≤ t ∧ t < b), (if nxt D t ≤ ρ then nxt D t - t else 0)
      = max a (min ρ b) - a := by
  classical
  rw [← Finset.sum_filter, Finset.filter_filter]
  by_cases hρa : ρ ≤ a
  · rw [max_eq_left (min_le_of_left_le hρa), sub_self]
    apply Finset.sum_eq_zero
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨_, ⟨hat, htb⟩, hn⟩ := ht
    have h1 := le_nxt D t
    have : nxt D t = t := by linarith
    rw [this, sub_self]
  · push_neg at hρa
    have hc : min ρ b ∈ D := by rcases min_choice ρ b with h | h <;> rw [h] <;> assumption
    rw [max_eq_right (le_min (le_of_lt hρa) hab)]
    rw [← tele' D a (min ρ b) ha hc (le_min (le_of_lt hρa) hab)]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨htD, ⟨hat, htb⟩, hn⟩
      refine ⟨htD, hat, lt_min ?_ htb⟩
      have : t < nxt D t := by
        unfold nxt
        rw [dif_pos ⟨b, Finset.mem_filter.mpr ⟨hb, htb⟩⟩]
        exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2
      linarith
    · rintro ⟨htD, hat, htm⟩
      refine ⟨htD, ⟨hat, lt_of_lt_of_le htm (min_le_right _ _)⟩, ?_⟩
      exact (nxt_le D t _ hc htm).trans (min_le_left _ _)

end MTSPLayer



open scoped Classical

namespace MTSP54
open MetricTSPSublinear SimpleGraph MTSPHelly MTSPWL1 MTSPLayer Finset

variable {n : ℕ} {S : Finset (Fin n)}

lemma weight_eq (C : SteinerTree S) :
    C.weight = ∑ e ∈ Es C.T.G, C.T.w s(e.1, e.2) := by
  unfold SteinerTree.weight SteinerTree.edges
  have h3 : (Es C.T.G).image (fun e => s(e.1, e.2)) =
      Finset.univ.filter (fun e => e ∈ C.T.G.edgeSet) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, he, rfl⟩; exact ((mem_Es C.T.G).mp he).2
    · intro hxG
      induction x using Sym2.ind with
      | h x y =>
        have hxy : C.T.G.Adj x y := hxG
        rcases lt_or_gt_of_ne hxy.ne with hlt | hlt
        · exact ⟨(x, y), (mem_Es C.T.G).mpr ⟨hlt, hxy⟩, rfl⟩
        · exact ⟨(y, x), (mem_Es C.T.G).mpr ⟨hlt, hxy.symm⟩, Sym2.eq_swap⟩
  rw [← h3, Finset.sum_image]
  intro e he f hf hef
  by_contra hne
  exact pair_ne_of_ne C.T.G he hf (Ne.symm hne) hef.symm

theorem core (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (C : SteinerTree S)
    (q : Fin n → RPoint C.T.G) (hqS : ∀ s ∈ S, q s = RPoint.vtx (C.ι s))
    (hq : ∀ u v, rdist C.T (q u) (q v) ≤ d u v) :
    C.weight ≤ cutLP d Finset.univ := by
  set w : Fin C.m × Fin C.m → ℝ := fun e => C.T.w s(e.1, e.2) with hw
  set Θ : Fin C.m × Fin C.m → Finset ℝ := fun e =>
    insert 0 (insert 1 (Finset.univ.image (fun v => cr C.T.G (q v) e))) with hΘ
  have h0 : ∀ e, (0 : ℝ) ∈ Θ e := fun e => Finset.mem_insert_self _ _
  have h1 : ∀ e, (1 : ℝ) ∈ Θ e := fun e => Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hcrΘ : ∀ e v, cr C.T.G (q v) e ∈ Θ e := fun e v =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (mem_univ v)))
  set pos : Fin C.m × Fin C.m → Finset ℝ := fun e => (Θ e).filter (fun t => 0 ≤ t ∧ t < 1)
    with hpos
  set cutA : Fin C.m × Fin C.m → ℝ → Finset (Fin n) := fun e t =>
    Finset.univ.filter (fun v => nxt (Θ e) t ≤ cr C.T.G (q v) e) with hcutA
  set y : Finset (Fin n) → ℝ := fun A =>
    ∑ e ∈ Es C.T.G, ∑ t ∈ pos e, if cutA e t = A then w e * (nxt (Θ e) t - t) else 0 with hy
  have hwnn : ∀ e ∈ Es C.T.G, 0 ≤ w e := fun e he => w_nn C.T he
  have hnxt_lt : ∀ e, ∀ t ∈ pos e, t < nxt (Θ e) t := by
    intro e t ht
    rw [Finset.mem_filter] at ht
    unfold nxt
    rw [dif_pos ⟨1, Finset.mem_filter.mpr ⟨h1 e, ht.2.2⟩⟩]
    exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2
  have hnxt_le1 : ∀ e, ∀ t ∈ pos e, nxt (Θ e) t ≤ 1 := by
    intro e t ht
    rw [Finset.mem_filter] at ht
    exact nxt_le _ _ _ (h1 e) ht.2.2
  -- per-edge layer cake
  have hlayer : ∀ e, ∀ x ∈ Θ e, 0 ≤ x → x ≤ 1 →
      ∑ t ∈ pos e, (if nxt (Θ e) t ≤ x then nxt (Θ e) t - t else 0) = x := by
    intro e x hx hx0 hx1
    rw [hpos, tele_cap (Θ e) 0 1 x (h0 e) (h1 e) hx zero_le_one]
    rw [min_eq_left hx1, max_eq_right hx0]; ring
  have hfeas : IsDualFeasible d Finset.univ y := by
    refine ⟨?_, ?_, ?_⟩
    · intro A
      apply Finset.sum_nonneg; intro e he
      apply Finset.sum_nonneg; intro t ht
      split_ifs
      · exact mul_nonneg (hwnn e he) (by linarith [hnxt_lt e t ht])
      · exact le_refl _
    · intro A hA
      apply Finset.sum_eq_zero; intro e he
      apply Finset.sum_eq_zero; intro t ht
      rw [if_neg]
      intro hcA
      apply hA
      subst hcA
      obtain ⟨hlt, hadj⟩ := (mem_Es C.T.G).mp he
      refine ⟨Finset.subset_univ _, ?_, ?_⟩
      · obtain ⟨c, hbc, hleaf⟩ := MTSPTree.exists_leaf_behind C.T.isTree hadj
        obtain ⟨s1, hs1, hs1c⟩ := C.leaves c hleaf
        refine ⟨s1, Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
        rw [hqS s1 hs1, hs1c]
        have : sd C.T.G e c = 1 := by
          unfold sd
          rw [if_neg]
          intro hac
          exact MTSPTree.not_reach_of_adj C.T.isTree.isAcyclic hadj (hac.trans hbc.symm)
        show nxt (Θ e) t ≤ sd C.T.G e c
        rw [this]; exact hnxt_le1 e t ht
      · intro hU
        obtain ⟨c, hac, hleaf⟩ := MTSPTree.exists_leaf_behind C.T.isTree hadj.symm
        rw [Sym2.eq_swap] at hac
        obtain ⟨s2, hs2, hs2c⟩ := C.leaves c hleaf
        have hmem : s2 ∈ cutA e t := by rw [hU]; exact mem_univ _
        rw [Finset.mem_filter, hqS s2 hs2, hs2c] at hmem
        have : sd C.T.G e c = 0 := by unfold sd; rw [if_pos hac]
        have h2 := hmem.2
        change nxt (Θ e) t ≤ sd C.T.G e c at h2
        rw [this] at h2
        have := hnxt_lt e t ht
        have : 0 ≤ t := (Finset.mem_filter.mp ht).2.1
        linarith
    · intro u _ v _ _
      have key : ∀ e ∈ Es C.T.G,
          ∑ t ∈ pos e, (if ¬ ((u ∈ cutA e t) ↔ (v ∈ cutA e t)) then w e * (nxt (Θ e) t - t) else 0)
            = w e * |cr C.T.G (q u) e - cr C.T.G (q v) e| := by
        intro e _
        set x := cr C.T.G (q u) e
        set z := cr C.T.G (q v) e
        have hx := cr_mem C.T (q u) e
        have hz := cr_mem C.T (q v) e
        have hm : min x z ∈ Θ e := by
          rcases min_choice x z with h | h <;> rw [h]
          · exact hcrΘ e u
          · exact hcrΘ e v
        have hpt : ∀ t, (if ¬ ((u ∈ cutA e t) ↔ (v ∈ cutA e t)) then w e * (nxt (Θ e) t - t) else 0)
            = w e * ((if nxt (Θ e) t ≤ x then nxt (Θ e) t - t else 0) +
                (if nxt (Θ e) t ≤ z then nxt (Θ e) t - t else 0) -
                2 * (if nxt (Θ e) t ≤ min x z then nxt (Θ e) t - t else 0)) := by
          intro t
          have hu' : (u ∈ cutA e t) ↔ nxt (Θ e) t ≤ x := by
            simp only [hcutA, Finset.mem_filter, Finset.mem_univ, true_and]; rfl
          have hv' : (v ∈ cutA e t) ↔ nxt (Θ e) t ≤ z := by
            simp only [hcutA, Finset.mem_filter, Finset.mem_univ, true_and]; rfl
          rw [if_congr (not_congr (iff_congr hu' hv')) rfl rfl]
          simp only [le_min_iff]
          by_cases ha : nxt (Θ e) t ≤ x <;> by_cases hb : nxt (Θ e) t ≤ z <;> simp [ha, hb] <;> ring_nf <;> simp
        rw [Finset.sum_congr rfl (fun t _ => hpt t), ← Finset.mul_sum, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum, hlayer e x (hcrΘ e u) hx.1 hx.2,
          hlayer e z (hcrΘ e v) hz.1 hz.2,
          hlayer e (min x z) hm (le_min hx.1 hz.1) ((min_le_left _ _).trans hx.2)]
        congr 1
        rcases le_total x z with h | h
        · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
        · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
      calc ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => ¬ ((u ∈ A) ↔ (v ∈ A))), y A
          = ∑ e ∈ Es C.T.G, ∑ t ∈ pos e,
              (if ¬ ((u ∈ cutA e t) ↔ (v ∈ cutA e t)) then w e * (nxt (Θ e) t - t) else 0) := by
            rw [hy]; simp only
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro e _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro t _
            rw [Finset.sum_ite_eq]
            apply if_congr _ rfl rfl
            simp
        _ = L C.T (q u) (q v) := by
            unfold L
            exact Finset.sum_congr rfl key
        _ ≤ rdist C.T (q u) (q v) := L_le_rdist C.T _ _
        _ ≤ d u v := hq u v
  have htot : ∑ A, y A = C.weight := by
    rw [weight_eq, hy]; simp only
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.sum_comm]
    have : ∀ t, ∑ A : Finset (Fin n), (if cutA e t = A then w e * (nxt (Θ e) t - t) else 0)
        = w e * (nxt (Θ e) t - t) := fun t => by rw [Finset.sum_ite_eq]; simp
    rw [Finset.sum_congr rfl (fun t _ => this t), ← Finset.mul_sum, hpos,
      tele' (Θ e) 0 1 (h0 e) (h1 e) zero_le_one]
    ring
  rw [← htot]
  exact MTSPDual.weak_duality d hd Finset.univ y hfeas

end MTSP54



/-! Infrastructure for Lemma 5.3: tree distances, points along root paths, distance bounds. -/

namespace Q53
open MetricTSPSublinear SimpleGraph

variable {m : ℕ} (T : TreeCoverLB.WeightedTree (Fin m))

/-- Weight of a walk. -/
noncomputable def L {a b : Fin m} (p : T.G.Walk a b) : ℝ :=
  KServer.walkWeight (fun u v => T.w s(u, v)) p

lemma L_nil (a : Fin m) : L T (Walk.nil : T.G.Walk a a) = 0 := by
  simp [L, KServer.walkWeight]

lemma L_cons {a b c : Fin m} (h : T.G.Adj a b) (p : T.G.Walk b c) :
    L T (Walk.cons h p) = T.w s(a, b) + L T p := by
  simp [L, KServer.walkWeight]

lemma L_append {a b c : Fin m} (p : T.G.Walk a b) (q : T.G.Walk b c) :
    L T (p.append q) = L T p + L T q := by
  simp [L, KServer.walkWeight, Walk.darts_append]

lemma L_reverse {a b : Fin m} (p : T.G.Walk a b) : L T p.reverse = L T p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [Walk.reverse_cons, L_append, ih, L_cons, L_cons, L_nil, Sym2.eq_swap]; ring

lemma L_nonneg {a b : Fin m} (p : T.G.Walk a b) : 0 ≤ L T p := by
  induction p with
  | nil => rw [L_nil]
  | cons h p ih => rw [L_cons]; exact add_nonneg (T.w_nonneg _ h) ih

lemma path_isPath (a b : Fin m) : (T.path a b).IsPath :=
  (T.isTree.existsUnique_path a b).exists.choose_spec

lemma dist_def (a b : Fin m) : T.dist a b = L T (T.path a b) := rfl

lemma dist_eq_L {a b : Fin m} (p : T.G.Walk a b) (hp : p.IsPath) : T.dist a b = L T p := by
  have := (T.isTree.existsUnique_path a b).unique (path_isPath T a b) hp
  rw [dist_def, this]

lemma dist_self (a : Fin m) : T.dist a a = 0 := by
  rw [dist_eq_L T Walk.nil Walk.IsPath.nil, L_nil]

lemma dist_comm (a b : Fin m) : T.dist a b = T.dist b a := by
  rw [dist_eq_L T _ (path_isPath T a b).reverse, L_reverse, dist_def]

lemma dist_adj {a b : Fin m} (h : T.G.Adj a b) : T.dist a b = T.w s(a, b) := by
  have hp : (Walk.cons h Walk.nil : T.G.Walk a b).IsPath :=
    (Walk.cons_isPath_iff _ _).mpr ⟨Walk.IsPath.nil, by simp [h.ne]⟩
  rw [dist_eq_L T _ hp, L_cons, L_nil, add_zero]

lemma dist_triangle (a b c : Fin m) : T.dist a c ≤ T.dist a b + T.dist b c := by
  let W := (T.path a b).append (T.path b c)
  rw [dist_eq_L T W.bypass W.bypass_isPath, dist_def T a b, dist_def T b c, ← L_append]
  unfold L KServer.walkWeight
  apply List.Sublist.sum_le_sum ((W.darts_bypass_sublist_darts).map _)
  intro x hx
  obtain ⟨dd, _, rfl⟩ := List.mem_map.mp hx
  exact T.w_nonneg _ dd.adj

lemma dist_nonneg (a b : Fin m) : 0 ≤ T.dist a b := by
  have := dist_triangle T a b a
  rw [dist_self, dist_comm T b a] at this
  linarith

lemma dist_split {x y z : Fin m} (hz : z ∈ (T.path x y).support) :
    T.dist x y = T.dist x z + T.dist z y := by
  have hp := path_isPath T x y
  rw [dist_eq_L T _ (hp.takeUntil hz), dist_eq_L T _ (hp.dropUntil hz), ← L_append,
    Walk.take_spec, dist_def]

/-- The bridge decomposition of distances across an edge. -/
lemma bridge {a a1 z y : Fin m} (h : T.G.Adj a a1)
    (hz : (T.G.deleteEdges {s(a, a1)}).Reachable z a)
    (hy : (T.G.deleteEdges {s(a, a1)}).Reachable a1 y) :
    T.dist z y = T.dist z a + T.w s(a, a1) + T.dist a1 y := by
  have hna : ¬ (T.G.deleteEdges {s(a, a1)}).Reachable a a1 :=
    MTSPTree.not_reach_of_adj T.isTree.isAcyclic h
  have h1 : s(a, a1) ∈ (T.path z y).edges := by
    rw [MTSPTree.mem_path_edges_iff T.isTree _ (path_isPath T z y)]
    intro hzy; exact hna (hz.symm.trans (hzy.trans hy.symm))
  have h2 : s(a, a1) ∈ (T.path a y).edges := by
    rw [MTSPTree.mem_path_edges_iff T.isTree _ (path_isPath T a y)]
    intro hay; exact hna (hay.trans hy.symm)
  rw [dist_split T ((T.path z y).fst_mem_support_of_mem_edges h1),
    dist_split T (z := a1) ((T.path a y).snd_mem_support_of_mem_edges h2), dist_adj T h]
  ring

lemma reach_cons {a a1 y : Fin m} (h : T.G.Adj a a1) (p : T.G.Walk a1 y)
    (hp : (Walk.cons h p).IsPath) : (T.G.deleteEdges {s(a, a1)}).Reachable a1 y :=
  ⟨p.toDeleteEdge _ (fun he => ((Walk.cons_isPath_iff h p).mp hp).2
    (p.fst_mem_support_of_mem_edges he))⟩

/-! ### Points of `R(T)` -/

/-- The point at fraction `β` from `a` on the edge `{a, b}`. -/
noncomputable def edgePt {a b : Fin m} (h : T.G.Adj a b) (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    RPoint T.G :=
  if hlt : a < b then RPoint.inner a b h hlt β hβ
  else RPoint.inner b a h.symm (lt_of_le_of_ne (not_lt.mp hlt) h.ne.symm) (1 - β)
    ⟨by linarith [hβ.2], by linarith [hβ.1]⟩

lemma rdist_edgePt_vtx {a b : Fin m} (h : T.G.Adj a b) (β : ℝ) (hβ : 0 < β ∧ β < 1) (c : Fin m) :
    rdist T (edgePt T h β hβ) (RPoint.vtx c) =
      min (β * T.w s(a, b) + T.dist a c) ((1 - β) * T.w s(a, b) + T.dist b c) := by
  unfold edgePt
  split_ifs with hlt
  · simp only [rdist]
  · simp only [rdist]
    rw [Sym2.eq_swap, min_comm]
    congr 2; ring

lemma rdist_edgePt_same {a b : Fin m} (h : T.G.Adj a b) (β β' : ℝ) (hβ : 0 < β ∧ β < 1)
    (hβ' : 0 < β' ∧ β' < 1) :
    rdist T (edgePt T h β hβ) (edgePt T h β' hβ') = |β - β'| * T.w s(a, b) := by
  unfold edgePt
  split_ifs with hlt
  · simp only [rdist, and_self, if_true]
  · simp only [rdist, and_self, if_true]
    rw [Sym2.eq_swap]
    congr 1
    rw [show 1 - β - (1 - β') = -(β - β') by ring, abs_neg]

lemma rdist_comm (P Q : RPoint T.G) : rdist T P Q = rdist T Q P := by
  cases P with
  | vtx a =>
    cases Q with
    | vtx b => simp only [rdist]; exact dist_comm T a b
    | inner b e hbe hlt β hβ => simp only [rdist]
  | inner a b hab hlt α hα =>
    cases Q with
    | vtx c => simp only [rdist]
    | inner c e hce hlt' β hβ =>
      simp only [rdist]
      by_cases h : a = c ∧ b = e
      · obtain ⟨rfl, rfl⟩ := h
        simp [abs_sub_comm]
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), min_min_min_comm
          (β * T.w s(c, e) + T.dist c a + α * T.w s(a, b))]
        rw [dist_comm T a c, dist_comm T a e, dist_comm T b c, dist_comm T b e]
        congr 2 <;> ring

lemma le_min_add_min {A B C D X : ℝ} (h1 : X ≤ A + C) (h2 : X ≤ A + D) (h3 : X ≤ B + C)
    (h4 : X ≤ B + D) : X ≤ min A B + min C D := by
  rcases le_total A B with h | h <;> rcases le_total C D with h' | h' <;>
    simp only [min_eq_left, min_eq_right, h, h'] <;> assumption

lemma min_le_add_min_left {A B C D X : ℝ} (h1 : A ≤ X + C) (h2 : B ≤ X + D) :
    min A B ≤ X + min C D := by
  rcases le_total C D with h | h
  · rw [min_eq_left h]; exact (min_le_left _ _).trans h1
  · rw [min_eq_right h]; exact (min_le_right _ _).trans h2

lemma min_le_add_min_right {A B C D X : ℝ} (h1 : A ≤ C + X) (h2 : B ≤ D + X) :
    min A B ≤ min C D + X := by
  rcases le_total C D with h | h
  · rw [min_eq_left h]; exact (min_le_left _ _).trans h1
  · rw [min_eq_right h]; exact (min_le_right _ _).trans h2

/-- Triangle inequality through a node. -/
lemma rdist_tri (P Q : RPoint T.G) (c : Fin m) :
    rdist T P Q ≤ rdist T P (RPoint.vtx c) + rdist T (RPoint.vtx c) Q := by
  cases P with
  | vtx a =>
    cases Q with
    | vtx b => simp only [rdist]; exact dist_triangle T a c b
    | inner b e hbe hlt β hβ =>
      simp only [rdist]
      apply min_le_add_min_left
      · linarith [dist_triangle T b c a, dist_comm T c a]
      · linarith [dist_triangle T e c a, dist_comm T c a]
  | inner a b hab hlt α hα =>
    cases Q with
    | vtx e =>
      simp only [rdist]
      apply min_le_add_min_right
      · linarith [dist_triangle T a c e]
      · linarith [dist_triangle T b c e]
    | inner c' e hce hlt' β hβ =>
      simp only [rdist]
      have hw := T.w_nonneg s(a, b) hab
      have hw' := T.w_nonneg s(c', e) hce
      by_cases h : a = c' ∧ b = e
      · obtain ⟨rfl, rfl⟩ := h
        rw [if_pos ⟨rfl, rfl⟩]
        have hab' := dist_adj T hab
        have t1 := dist_triangle T a c b
        have n1 := dist_nonneg T a c
        have n2 := dist_nonneg T b c
        have dc := dist_comm T c b
        have p1 := mul_nonneg hα.1.le hw
        have p2 := mul_nonneg hβ.1.le hw
        have p3 := mul_nonneg (sub_nonneg.mpr hα.2.le) hw
        have p4 := mul_nonneg (sub_nonneg.mpr hβ.2.le) hw
        rcases abs_cases (α - β) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] <;>
          apply le_min_add_min <;> nlinarith
      · rw [if_neg h]
        have t1 := dist_triangle T a c c'
        have t2 := dist_triangle T a c e
        have t3 := dist_triangle T b c c'
        have t4 := dist_triangle T b c e
        have c1 := dist_comm T c c'
        have c2 := dist_comm T c e
        apply le_min_add_min
        · exact min_le_of_left_le (min_le_of_left_le (by linarith))
        · exact min_le_of_left_le (min_le_of_right_le (by linarith))
        · exact min_le_of_right_le (min_le_of_left_le (by linarith))
        · exact min_le_of_right_le (min_le_of_right_le (by linarith))

/-! ### The point at depth `x` along a walk -/

/-- The point at depth `x` (from the start) along the walk `p` (clamped to the ends). -/
noncomputable def wp : {a y : Fin m} → T.G.Walk a y → ℝ → RPoint T.G
  | a, _, Walk.nil, _ => RPoint.vtx a
  | a, _, Walk.cons (v := b) h p, x =>
    if hx : x < T.w s(a, b) then
      (if hx0 : x ≤ 0 then RPoint.vtx a
       else edgePt T h (x / T.w s(a, b))
        ⟨div_pos (not_le.mp hx0) (lt_trans (not_le.mp hx0) hx),
          (div_lt_one (lt_trans (not_le.mp hx0) hx)).mpr hx⟩)
    else wp p (x - T.w s(a, b))

lemma wp_nil (a : Fin m) (x : ℝ) : wp T (Walk.nil : T.G.Walk a a) x = RPoint.vtx a := by
  rw [wp]

lemma wp_cons_rec {a b c : Fin m} (h : T.G.Adj a b) (p : T.G.Walk b c) (x : ℝ)
    (hx : ¬ x < T.w s(a, b)) : wp T (Walk.cons h p) x = wp T p (x - T.w s(a, b)) := by
  rw [wp, dif_neg hx]

lemma wp_cons_edge {a b c : Fin m} (h : T.G.Adj a b) (p : T.G.Walk b c) (x : ℝ)
    (hx0 : 0 < x) (hx : x < T.w s(a, b)) :
    ∃ hβ, wp T (Walk.cons h p) x = edgePt T h (x / T.w s(a, b)) hβ := by
  rw [wp, dif_pos hx, dif_neg (not_le.mpr hx0)]
  exact ⟨_, rfl⟩

lemma wp_end {a y : Fin m} (p : T.G.Walk a y) (x : ℝ) (hx : L T p ≤ x) :
    wp T p x = RPoint.vtx y := by
  induction p generalizing x with
  | nil => rw [wp]
  | cons h p ih =>
    rw [L_cons] at hx
    have := L_nonneg T p
    rw [wp_cons_rec T h p x (by linarith)]
    exact ih _ (by linarith)

/-- **Lemma A.** Distance from a point on a path to a node. -/
lemma wp_A {a y : Fin m} (p : T.G.Walk a y) (hp : p.IsPath) (z : Fin m) (x : ℝ) :
    rdist T (wp T p x) (RPoint.vtx z) ≤ max (T.dist a z - x) (x - L T p + T.dist y z) := by
  induction p generalizing x with
  | nil =>
    simp only [wp, rdist, L_nil]
    rcases le_total 0 x with hx | hx
    · exact le_max_of_le_right (by linarith)
    · exact le_max_of_le_left (by linarith)
  | @cons a a1 y h p' ih =>
    have hp' := ((Walk.cons_isPath_iff h p').mp hp).1
    have hLp' : L T p' = T.dist a1 y := (dist_eq_L T p' hp').symm
    have hR := reach_cons T h p' hp
    rw [L_cons, hLp']
    have side : (T.dist y z = T.dist a z + T.w s(a, a1) + T.dist a1 y ∧
        T.dist a1 z = T.dist a z + T.w s(a, a1)) ∨
        T.dist a z = T.w s(a, a1) + T.dist a1 z := by
      rcases MTSPTree.reach_or_reach T.isTree.connected (a := a) (b := a1) z with hz | hz
      · left
        have e1 := bridge T h hz hR
        have e2 := bridge T h hz (Reachable.refl a1)
        rw [dist_self] at e2
        rw [dist_comm T y z, e1, dist_comm T a1 z, e2, dist_comm T z a]
        constructor <;> ring
      · right
        have e := bridge T h (Reachable.refl a) hz.symm
        rw [dist_self] at e
        rw [e]; ring
    rw [wp]
    split_ifs with hx hx0
    · simp only [rdist]; exact le_max_of_le_left (by linarith)
    · have hx0' : 0 < x := not_le.mp hx0
      have hwpos : 0 < T.w s(a, a1) := lt_trans hx0' hx
      rw [rdist_edgePt_vtx]
      have e1 : x / T.w s(a, a1) * T.w s(a, a1) = x := div_mul_cancel₀ x hwpos.ne'
      have e2 : (1 - x / T.w s(a, a1)) * T.w s(a, a1) = T.w s(a, a1) - x := by
        rw [sub_mul, one_mul, e1]
      rw [e1, e2]
      rcases side with ⟨s1, s2⟩ | s1
      · exact (min_le_left _ _).trans (le_max_of_le_right (by linarith))
      · exact (min_le_right _ _).trans (le_max_of_le_left (by linarith))
    · have := ih hp' (x - T.w s(a, a1))
      rw [hLp'] at this
      refine this.trans (max_le ?_ ?_)
      · rcases side with ⟨s1, s2⟩ | s1
        · exact le_max_of_le_right (by linarith)
        · exact le_max_of_le_left (by linarith)
      · exact le_max_of_le_right (by linarith)

lemma wp_root {a y : Fin m} (p : T.G.Walk a y) (hp : p.IsPath) (x : ℝ) (hx : 0 ≤ x) :
    rdist T (wp T p x) (RPoint.vtx a) ≤ x := by
  have := wp_A T p hp a x
  rw [dist_self, dist_comm T y a, dist_eq_L T p hp] at this
  refine this.trans (max_le (by linarith) (by linarith))

lemma wp_B0 {a y z : Fin m} (p : T.G.Walk a y) (hp : p.IsPath) (q : T.G.Walk a z)
    (hq : q.IsPath) (x x' : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x') :
    rdist T (wp T p x) (wp T q x') ≤ x + x' :=
  (rdist_tri T _ _ a).trans (add_le_add (wp_root T p hp x hx)
    (by rw [rdist_comm]; exact wp_root T q hq x' hx'))

lemma wp_mix {a a1 z : Fin m} (h : T.G.Adj a a1) (q : T.G.Walk a1 z) (hq : q.IsPath)
    (x x' : ℝ) (hβ : 0 < x / T.w s(a, a1) ∧ x / T.w s(a, a1) < 1) (hx0 : 0 < x)
    (hx : x < T.w s(a, a1)) (hx' : T.w s(a, a1) ≤ x') :
    rdist T (edgePt T h (x / T.w s(a, a1)) hβ) (wp T q (x' - T.w s(a, a1))) ≤ x' - x := by
  have hwpos : 0 < T.w s(a, a1) := lt_trans hx0 hx
  refine (rdist_tri T _ _ a1).trans ?_
  rw [rdist_edgePt_vtx, rdist_comm T (RPoint.vtx a1)]
  have h2 := wp_root T q hq (x' - T.w s(a, a1)) (by linarith)
  have e1 : x / T.w s(a, a1) * T.w s(a, a1) = x := div_mul_cancel₀ x hwpos.ne'
  have e2 : (1 - x / T.w s(a, a1)) * T.w s(a, a1) = T.w s(a, a1) - x := by
    rw [sub_mul, one_mul, e1]
  rw [e2, dist_self]
  have := min_le_right (x / T.w s(a, a1) * T.w s(a, a1) + T.dist a a1) (T.w s(a, a1) - x + 0)
  linarith

/-- **Lemma B.** Distance between points on two paths from a common root. -/
lemma wp_B {a y : Fin m} (p : T.G.Walk a y) (hp : p.IsPath) {z : Fin m} (q : T.G.Walk a z)
    (hq : q.IsPath) (x x' : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x') :
    rdist T (wp T p x) (wp T q x') ≤ max |x - x'| (x + x' - L T p - L T q + T.dist y z) := by
  induction p generalizing z x x' with
  | nil =>
    refine le_max_of_le_right ((wp_B0 T _ hp q hq x x' hx hx').trans (le_of_eq ?_))
    rw [L_nil, dist_eq_L T q hq]; ring
  | @cons a a1 y h p' ih =>
    have hp' := ((Walk.cons_isPath_iff h p').mp hp).1
    -- the trivial cases `x = 0` or `x' = 0`
    by_cases h0 : x = 0 ∨ x' = 0
    · refine le_max_of_le_left ((wp_B0 T _ hp q hq x x' hx hx').trans ?_)
      rcases h0 with rfl | rfl
      · rw [zero_sub, abs_neg, abs_of_nonneg hx']; linarith
      · rw [sub_zero, abs_of_nonneg hx]; linarith
    push Not at h0
    have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm h0.1)
    have hxp' : 0 < x' := lt_of_le_of_ne hx' (Ne.symm h0.2)
    cases q with
    | nil =>
      refine le_max_of_le_right ((wp_B0 T _ hp _ hq x x' hx hx').trans (le_of_eq ?_))
      rw [L_nil, dist_comm, dist_eq_L T _ hp]; ring
    | @cons _ b1 _ h2 q' =>
      have hq' := ((Walk.cons_isPath_iff h2 q').mp hq).1
      by_cases hab : a1 = b1
      · subst hab
        have hw := T.w_nonneg s(a, a1) h
        by_cases hxw : x < T.w s(a, a1)
        · obtain ⟨hβ, e1⟩ := wp_cons_edge T h p' x hxp hxw
          rw [e1]
          by_cases hxw' : x' < T.w s(a, a1)
          · obtain ⟨hβ', e2⟩ := wp_cons_edge T h2 q' x' hxp' hxw'
            rw [e2, rdist_edgePt_same, ← sub_div, abs_div,
              abs_of_pos (lt_trans hxp hxw), div_mul_cancel₀ _ (lt_trans hxp hxw).ne']
            exact le_max_left _ _
          · rw [wp_cons_rec T h2 q' x' hxw']
            refine le_max_of_le_left ((wp_mix T h q' hq' x x' hβ hxp hxw (not_lt.mp hxw')).trans ?_)
            rw [abs_sub_comm]; exact le_abs_self _
        · rw [wp_cons_rec T h p' x hxw]
          by_cases hxw' : x' < T.w s(a, a1)
          · obtain ⟨hβ', e2⟩ := wp_cons_edge T h2 q' x' hxp' hxw'
            rw [e2, rdist_comm]
            refine le_max_of_le_left ((wp_mix T h p' hp' x' x hβ' hxp' hxw' (not_lt.mp hxw)).trans ?_)
            exact le_abs_self _
          · rw [wp_cons_rec T h2 q' x' hxw']
            have := ih hp' q' hq' (x - T.w s(a, a1)) (x' - T.w s(a, a1)) (by linarith)
              (by linarith)
            rw [L_cons, L_cons]
            refine this.trans (le_of_eq ?_)
            congr 1
            · congr 1; ring
            · ring
      · -- the paths diverge at `a`
        have hR := reach_cons T h p' hp
        have hz : (T.G.deleteEdges {s(a, a1)}).Reachable z a := by
          refine Reachable.symm ⟨(Walk.cons h2 q').toDeleteEdge _ ?_⟩
          rw [Walk.edges_cons, List.mem_cons, not_or]
          refine ⟨?_, fun he => ((Walk.cons_isPath_iff h2 q').mp hq).2
            (q'.fst_mem_support_of_mem_edges he)⟩
          intro he
          rcases Sym2.eq_iff.mp he with ⟨_, h'⟩ | ⟨_, h'⟩
          · exact hab h'
          · exact h.ne h'.symm
        have e := bridge T h hz hR
        refine le_max_of_le_right ((wp_B0 T _ hp _ hq x x' hx hx').trans (le_of_eq ?_))
        rw [dist_comm T y z, e, dist_comm T z a, dist_eq_L T _ hq, dist_eq_L T _ hp', L_cons]
        ring

end Q53



/-! Lemma 5.3 of Azarmehr–Behnezhad: the map `q : V → R(C)`. -/

namespace Q53
open MetricTSPSublinear SimpleGraph

variable {n : ℕ} {S : Finset (Fin n)}

section
variable (d : Fin n → Fin n → ℝ) (C : SteinerTree S) (s₀ : Fin n) (hs₀ : s₀ ∈ S)

/-- The root `r = ι s₀`. -/
noncomputable def root : Fin C.m := C.ι s₀

/-- The depth `D(r, ι t)` of a terminal. -/
noncomputable def Ldep (t : {s // s ∈ S}) : ℝ := C.T.dist (root C s₀) (C.ι t)

/-- A maximiser `t*` of `t ↦ D(r, ι t) − f t`. -/
noncomputable def tstar (f : {s // s ∈ S} → ℝ) : {s // s ∈ S} :=
  haveI : Nonempty {s // s ∈ S} := ⟨⟨s₀, hs₀⟩⟩
  Classical.choose (Finite.exists_max (fun t => Ldep C s₀ t - f t))

lemma tstar_spec (f : {s // s ∈ S} → ℝ) (t : {s // s ∈ S}) :
    Ldep C s₀ t - f t ≤ Ldep C s₀ (tstar C s₀ hs₀ f) - f (tstar C s₀ hs₀ f) :=
  haveI : Nonempty {s // s ∈ S} := ⟨⟨s₀, hs₀⟩⟩
  Classical.choose_spec (Finite.exists_max (fun t => Ldep C s₀ t - f t)) t

/-- `ρ(f) = max_t (D(r, ι t) − f t)`. -/
noncomputable def rho (f : {s // s ∈ S} → ℝ) : ℝ :=
  Ldep C s₀ (tstar C s₀ hs₀ f) - f (tstar C s₀ hs₀ f)

/-- The map `Φ`. -/
noncomputable def Phi (f : {s // s ∈ S} → ℝ) : RPoint C.T.G :=
  if h : ∃ s ∈ S, f = (fun t : {s // s ∈ S} => d s t) then RPoint.vtx (C.ι (Classical.choose h))
  else wp C.T (C.T.path (root C s₀) (C.ι (tstar C s₀ hs₀ f))) (max (rho C s₀ hs₀ f) 0)

/-- The target terminal `τ v` of `q_v`. -/
noncomputable def tau (v : Fin n) : {s // s ∈ S} :=
  if h : v ∈ S then ⟨v, h⟩ else tstar C s₀ hs₀ (fun t => d v t)

/-- The depth `ρ' v` of `q_v` along the root path to `ι (τ v)`. -/
noncomputable def rhoP (v : Fin n) : ℝ :=
  if h : v ∈ S then Ldep C s₀ ⟨v, h⟩ else max (rho C s₀ hs₀ (fun t => d v t)) 0

/-- The depth of the branching node of the root paths to `ι (τ u)` and `ι (τ v)`
(Gromov product). -/
noncomputable def mu (u v : Fin n) : ℝ :=
  (Ldep C s₀ (tau d C s₀ hs₀ u) + Ldep C s₀ (tau d C s₀ hs₀ v) -
    C.T.dist (C.ι (tau d C s₀ hs₀ u)) (C.ι (tau d C s₀ hs₀ v))) / 2

variable {d C s₀ hs₀}

lemma Ldep_nonneg (t : {s // s ∈ S}) : 0 ≤ Ldep C s₀ t := dist_nonneg _ _ _

lemma dist_le_Ldep_add (a b : {s // s ∈ S}) :
    C.T.dist (C.ι a) (C.ι b) ≤ Ldep C s₀ a + Ldep C s₀ b := by
  unfold Ldep
  linarith [dist_triangle C.T (C.ι a) (root C s₀) (C.ι b), dist_comm C.T (C.ι a) (root C s₀)]

lemma Ldep_sub_le (a b : {s // s ∈ S}) :
    Ldep C s₀ b - Ldep C s₀ a ≤ C.T.dist (C.ι a) (C.ι b) := by
  have := dist_triangle C.T (root C s₀) (C.ι a) (C.ι b)
  unfold Ldep; linarith

variable (hd : DoublingMST.IsMetric d)
include hd

lemma d_self (x : Fin n) : d x x = 0 := (hd.1 x x).2 rfl

lemma d_nonneg (x y : Fin n) : 0 ≤ d x y := by
  have h1 := hd.2.2 x y x
  rw [d_self hd, hd.2.1 y x] at h1
  linarith

lemma Phi_eq (v : Fin n) :
    Phi d C s₀ hs₀ (fun t => d v t) =
      wp C.T (C.T.path (root C s₀) (C.ι (tau d C s₀ hs₀ v))) (rhoP d C s₀ hs₀ v) := by
  by_cases hv : v ∈ S
  · have hex : ∃ s ∈ S, (fun t : {s // s ∈ S} => d v t) = (fun t : {s // s ∈ S} => d s t) := ⟨v, hv, rfl⟩
    unfold Phi rhoP tau
    have hw : wp C.T (C.T.path (root C s₀) (C.ι ((⟨v, hv⟩ : {s // s ∈ S}) : Fin n)))
        (Ldep C s₀ ⟨v, hv⟩) = RPoint.vtx (C.ι v) := wp_end C.T _ _ (le_of_eq rfl)
    rw [dif_pos hex, dif_pos hv, dif_pos hv, hw]
    obtain ⟨hs, he⟩ := Classical.choose_spec hex
    have := congrFun he ⟨_, hs⟩
    simp only [d_self hd] at this
    rw [← ((hd.1 _ _).1 this)]
  · have hex : ¬ ∃ s ∈ S, (fun t : {s // s ∈ S} => d v t) = (fun t : {s // s ∈ S} => d s t) := by
      rintro ⟨s, hs, he⟩
      have := congrFun he ⟨s, hs⟩
      simp only [d_self hd] at this
      exact hv (((hd.1 _ _).1 this) ▸ hs)
    unfold Phi rhoP tau
    rw [dif_neg hex, dif_neg hv, dif_neg hv]

lemma rhoP_nonneg (v : Fin n) : 0 ≤ rhoP d C s₀ hs₀ v := by
  unfold rhoP
  split_ifs
  · exact Ldep_nonneg _
  · exact le_max_right _ _

lemma rhoP_le (v : Fin n) : rhoP d C s₀ hs₀ v ≤ Ldep C s₀ (tau d C s₀ hs₀ v) := by
  unfold rhoP tau
  split_ifs with hv
  · exact le_rfl
  · refine max_le ?_ (Ldep_nonneg _)
    unfold rho
    linarith [d_nonneg hd v (tstar C s₀ hs₀ (fun t => d v t))]

variable (hC : Dominated d C)
include hC

lemma dom (a b : {s // s ∈ S}) : C.T.dist (C.ι a) (C.ι b) ≤ d a b :=
  hC a a.2 b b.2

/-- The three facts about `q_v`. -/
lemma props (v : Fin n) :
    (∀ t : {s // s ∈ S}, Ldep C s₀ t - rhoP d C s₀ hs₀ v ≤ d v t) ∧
    (∀ t : {s // s ∈ S}, rhoP d C s₀ hs₀ v - Ldep C s₀ (tau d C s₀ hs₀ v) +
      C.T.dist (C.ι (tau d C s₀ hs₀ v)) (C.ι t) ≤ d v t) ∧
    (rhoP d C s₀ hs₀ v = 0 ∨
      rhoP d C s₀ hs₀ v + d v (tau d C s₀ hs₀ v) ≤ Ldep C s₀ (tau d C s₀ hs₀ v)) := by
  unfold rhoP tau
  by_cases hv : v ∈ S
  · simp only [dif_pos hv]
    refine ⟨fun t => ?_, fun t => ?_, Or.inr ?_⟩
    · have := Ldep_sub_le (C := C) (s₀ := s₀) ⟨v, hv⟩ t
      have := dom hd hC ⟨v, hv⟩ t
      simp only at this ⊢; linarith
    · have := dom hd hC ⟨v, hv⟩ t
      simp only at this ⊢; linarith
    · simp only [d_self hd]; linarith
  · simp only [dif_neg hv]
    set f : {s // s ∈ S} → ℝ := fun t => d v t with hf
    set ts := tstar C s₀ hs₀ f with hts
    have hspec := tstar_spec C s₀ hs₀ f
    have hrho : rho C s₀ hs₀ f = Ldep C s₀ ts - d v ts := rfl
    refine ⟨fun t => ?_, fun t => ?_, ?_⟩
    · have := hspec t
      have := le_max_left (rho C s₀ hs₀ f) 0
      rw [← hts] at *
      simp only [hf] at *
      linarith
    · rcases le_total 0 (rho C s₀ hs₀ f) with hr | hr
      · rw [max_eq_left hr, hrho]
        have h1 := dom hd hC ts t
        have h2 := hd.2.2 ts v t
        have h3 := hd.2.1 ts v
        linarith
      · rw [max_eq_right hr]
        have h1 := dist_le_Ldep_add (C := C) (s₀ := s₀) ts t
        have := hspec t
        rw [← hts] at this
        simp only [hf] at this
        linarith
    · rcases le_total 0 (rho C s₀ hs₀ f) with hr | hr
      · right; rw [max_eq_left hr, hrho]; linarith
      · left; exact max_eq_right hr

/-- The key inequality. -/
lemma key (u v : Fin n) :
    max |rhoP d C s₀ hs₀ u - rhoP d C s₀ hs₀ v|
      (rhoP d C s₀ hs₀ u + rhoP d C s₀ hs₀ v - Ldep C s₀ (tau d C s₀ hs₀ u) -
        Ldep C s₀ (tau d C s₀ hs₀ v) +
        C.T.dist (C.ι (tau d C s₀ hs₀ u)) (C.ι (tau d C s₀ hs₀ v))) ≤ d u v := by
  obtain ⟨u1, u2, u3⟩ := props (C := C) (s₀ := s₀) (hs₀ := hs₀) hd hC u
  obtain ⟨v1, v2, v3⟩ := props (C := C) (s₀ := s₀) (hs₀ := hs₀) hd hC v
  set x := rhoP d C s₀ hs₀ u
  set y := rhoP d C s₀ hs₀ v
  set tu := tau d C s₀ hs₀ u
  set tv := tau d C s₀ hs₀ v
  have hx := rhoP_nonneg (C := C) (s₀ := s₀) (hs₀ := hs₀) hd u
  have hy := rhoP_nonneg (C := C) (s₀ := s₀) (hs₀ := hs₀) hd v
  have huv := d_nonneg hd u v
  have hsym := hd.2.1 u v
  have tr1 := hd.2.2 v u tu
  have tr2 := hd.2.2 u v tv
  have hD := dist_le_Ldep_add (C := C) (s₀ := s₀) tu tv
  have hDc := dist_comm C.T (C.ι tu) (C.ι tv)
  have v1u := v1 tu
  have u1v := u1 tv
  have v2u := v2 tu
  have u2v := u2 tv
  have A : x - y ≤ d u v := by
    rcases u3 with h | h
    · linarith
    · linarith
  have B : y - x ≤ d u v := by
    rcases v3 with h | h
    · linarith
    · linarith
  refine max_le (abs_sub_le_iff.mpr ⟨A, B⟩) ?_
  rcases u3 with h | h
  · linarith
  · linarith

/-- The branching-node form of the key inequality:
`ρ' u + ρ' v − 2 min(ρ' u, ρ' v, μ u v) ≤ d u v`. -/
lemma branch_le (u v : Fin n) :
    rhoP d C s₀ hs₀ u + rhoP d C s₀ hs₀ v -
      2 * min (min (rhoP d C s₀ hs₀ u) (rhoP d C s₀ hs₀ v)) (mu d C s₀ hs₀ u v) ≤ d u v := by
  refine le_trans ?_ (key (C := C) (s₀ := s₀) (hs₀ := hs₀) hd hC u v)
  unfold mu
  set x := rhoP d C s₀ hs₀ u
  set y := rhoP d C s₀ hs₀ v
  rcases le_total (min x y) ((Ldep C s₀ (tau d C s₀ hs₀ u) + Ldep C s₀ (tau d C s₀ hs₀ v) -
    C.T.dist (C.ι (tau d C s₀ hs₀ u)) (C.ι (tau d C s₀ hs₀ v))) / 2) with h | h
  · rw [min_eq_left h]
    refine le_max_of_le_left ?_
    rcases le_total x y with h' | h'
    · rw [min_eq_left h', abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · rw [min_eq_right h', abs_of_nonneg (by linarith)]; linarith
  · rw [min_eq_right h]
    exact le_max_of_le_right (le_of_eq (by ring))

/-- Non-expansiveness of `q`. -/
lemma Phi_le (u v : Fin n) :
    rdist C.T (Phi d C s₀ hs₀ (fun t => d u t)) (Phi d C s₀ hs₀ (fun t => d v t)) ≤ d u v := by
  rw [Phi_eq (C := C) (s₀ := s₀) (hs₀ := hs₀) hd, Phi_eq (C := C) (s₀ := s₀) (hs₀ := hs₀) hd]
  exact (wp_B C.T _ (path_isPath _ _ _) _ (path_isPath _ _ _) _ _
    (rhoP_nonneg (C := C) (s₀ := s₀) (hs₀ := hs₀) hd u) (rhoP_nonneg (C := C) (s₀ := s₀) (hs₀ := hs₀) hd v)).trans (key (C := C) (s₀ := s₀) (hs₀ := hs₀) hd hC u v)

lemma Phi_vtx (s : Fin n) (hs : s ∈ S) :
    Phi d C s₀ hs₀ (fun t => d s t) = RPoint.vtx (C.ι s) := by
  rw [Phi_eq (C := C) (s₀ := s₀) (hs₀ := hs₀) hd]
  unfold rhoP tau
  rw [dif_pos hs, dif_pos hs]
  exact wp_end C.T _ _ (le_of_eq rfl)

end

end Q53

open MetricTSPSublinear in
theorem lemma_5_3_main {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (S : Finset (Fin n)) (C : SteinerTree S)
    (hC : Dominated d C) :
    ∃ Φ : ({s // s ∈ S} → ℝ) → RPoint C.T.G,
      (∀ s ∈ S, Φ (fun t => d s t) = RPoint.vtx (C.ι s)) ∧
      ∀ u v, rdist C.T (Φ (fun t => d u t)) (Φ (fun t => d v t)) ≤ d u v := by
  rcases S.eq_empty_or_nonempty with hS | ⟨s₀, hs₀⟩
  · obtain ⟨a⟩ := C.T.isTree.connected.nonempty
    refine ⟨fun _ => RPoint.vtx a, fun s hs => by simp [hS] at hs, fun u v => ?_⟩
    simp only [rdist, Q53.dist_self]
    exact Q53.d_nonneg hd u v
  · exact ⟨Q53.Phi d C s₀ hs₀, fun s hs => Q53.Phi_vtx (C := C) (s₀ := s₀) (hs₀ := hs₀) hd hC s hs,
      fun u v => Q53.Phi_le (C := C) (s₀ := s₀) (hs₀ := hs₀) hd hC u v⟩



namespace MTSPCor54
open MetricTSPSublinear Finset

theorem corollary_5_4_sol {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (S : Finset (Fin n)) : cutLP d S ≤ cutLP d Finset.univ := by
  rcases S.eq_empty_or_nonempty with hS | hSne
  · subst hS
    have h1 : cutLP d (∅ : Finset (Fin n)) ≤ 0 := by
      have := MTSPBridge.cutLP_le hd ∅ (fun _ => 0) ⟨fun _ => le_refl 0, fun A hA hAne hAS => by
        exact absurd (Finset.subset_empty.mp hA) (Finset.nonempty_iff_ne_empty.mp hAne)⟩
      simpa using this
    have h2 : 0 ≤ cutLP d (Finset.univ : Finset (Fin n)) :=
      MTSPBridge.le_cutLP univ 0 (fun x hx => MTSPBridge.cutLP_obj_nonneg hd univ x hx)
    linarith
  · obtain ⟨y, hy, hyK⟩ := MTSPDual.strong_duality d hd S
    obtain ⟨C, hC, hCw⟩ := MTSPL42.lemma_4_2_sol d hd S hSne y hy
    obtain ⟨Φ, hΦS, hΦ⟩ := lemma_5_3_main d hd S C hC
    have := MTSP54.core d hd C (fun v => Φ (fun t => d v t)) hΦS hΦ
    rw [hCw, hyK] at this
    exact this

end MTSPCor54


open MetricTSPSublinear

theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (S : Finset (Fin n)) :
    cutLP d S ≤ cutLP d Finset.univ :=
  MTSPCor54.corollary_5_4_sol d hd S
