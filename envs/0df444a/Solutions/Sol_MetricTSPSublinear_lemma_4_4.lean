-- Prove2me | solution 1 for MetricTSPSublinear.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:10:58.614552+00:00
-- url     : https://prove2.me/submissions/0405ba29-890a-48df-a51f-adc2658253d7

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
import Definitions.Def_MetricTSPSublinear_IsDominatedShortening
import Definitions.Def_DoublingMST_IsMSTOf
import Definitions.Def_MetricTSPSublinear_hull
import Theorems.Thm_MetricTSP_tour_of_connected


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



open scoped Classical

namespace MTSP43
open Finset MetricTSPSublinear SimpleGraph MTSPTree MTSPSteiner MTSPBridge

variable {n : ℕ}

/-- The `F`-edge `f` separates the endpoints of the pair `e`. -/
def crossF (F : SteinerTree (univ : Finset (Fin n))) (f : Sym2 (Fin F.m)) : Sym2 (Fin n) → Prop :=
  Sym2.lift ⟨fun u v => ¬ (F.T.G.deleteEdges {f}).Reachable (F.ι u) (F.ι v),
    fun u v => propext (not_congr reachable_comm)⟩

lemma crossF_mk (F : SteinerTree (univ : Finset (Fin n))) (f : Sym2 (Fin F.m)) (u v : Fin n) :
    crossF F f s(u, v) ↔ ¬ (F.T.G.deleteEdges {f}).Reachable (F.ι u) (F.ι v) := Iff.rfl

lemma pathWt_eq (F : SteinerTree (univ : Finset (Fin n))) (u v : Fin n) :
    F.pathWt (F.ι u) (F.ι v) =
      ∑ f ∈ F.edges, if crossF F f s(u, v) then F.T.w f else 0 := by
  classical
  unfold SteinerTree.pathWt
  rw [dist_eq_sum]
  apply Finset.sum_congr rfl
  intro f _
  apply if_congr _ rfl rfl
  rw [crossF_mk, ← mem_path_edges_iff F.T.isTree _ (path_isPath F _ _)]

lemma reachable_of_walk' (E : Finset (Sym2 (Fin n))) {u v : Fin n}
    (p : (DoublingMST.completeGraph n).Walk u v) (hp : ∀ e ∈ p.edges, e ∈ E) :
    (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).Reachable u v := by
  induction p with
  | nil => rfl
  | @cons a b c e h p ih =>
    have he : e = s(a, b) := h
    have heF : e ∈ E := hp e (by simp [CombOpt.SpanningTree.Graph.Walk.edges])
    have hrest := ih (fun e' he' => hp e' (by simp [CombOpt.SpanningTree.Graph.Walk.edges, he']))
    refine SimpleGraph.Reachable.trans ?_ hrest
    by_cases hab : a = b
    · rw [hab]
    · apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨by rw [← he]; exact heF, hab⟩

/-- Every edge of `F` is crossed by some edge of a spanning tree `E`. -/
lemma cover (F : SteinerTree (univ : Finset (Fin n))) (E : Finset (Sym2 (Fin n)))
    (hE : (DoublingMST.completeGraph n).IsSpanningTree E) (f : Sym2 (Fin F.m))
    (hf : f ∈ F.T.G.edgeSet) : ∃ e ∈ E, crossF F f e := by
  classical
  induction f with
  | _ a b =>
    have hadj : F.T.G.Adj a b := hf
    obtain ⟨c1, hbc1, hl1⟩ := exists_leaf_behind F.T.isTree hadj
    obtain ⟨c2, hac2, hl2⟩ := exists_leaf_behind F.T.isTree hadj.symm
    rw [Sym2.eq_swap] at hac2
    obtain ⟨s1, -, hs1⟩ := F.leaves c1 hl1
    obtain ⟨s2, -, hs2⟩ := F.leaves c2 hl2
    set R := (F.T.G.deleteEdges {s(a, b)}).Reachable with hR
    have hsep : ¬ R (F.ι s1) (F.ι s2) := by
      intro h
      rw [hs1, hs2] at h
      exact not_reach_of_adj F.T.isTree.isAcyclic hadj (hac2.trans (h.symm.trans hbc1.symm))
    obtain ⟨p, hp⟩ := hE.1 s1 s2
    set A : Finset (Fin n) := univ.filter (fun v => R (F.ι s1) (F.ι v)) with hA
    obtain ⟨e, he, hcut⟩ := walk_crosses A p (Finset.mem_filter.mpr ⟨mem_univ _, Reachable.refl _⟩) (by simpa [hA] using hsep)
    refine ⟨e, hp e he, ?_⟩
    unfold MetricTSPSublinear.cutEdges at hcut
    obtain ⟨⟨p1, q1⟩, hpq, rfl⟩ := Finset.mem_image.mp hcut
    simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and, hA,
      Finset.mem_filter] at hpq
    rw [crossF_mk]
    intro h
    exact hpq.2 (hpq.1.trans h)

lemma w_nonneg' (F : SteinerTree (univ : Finset (Fin n))) {f : Sym2 (Fin F.m)} (hf : f ∈ F.edges) :
    0 ≤ F.T.w f := F.T.w_nonneg f ((mem_edges_iff F f).mp hf)

/-- Reachability in the spanning-tree graph without `e0`, when no other edge crosses `f`, keeps the
`F`-side. -/
lemma side_const (F : SteinerTree (univ : Finset (Fin n))) (E : Finset (Sym2 (Fin n)))
    (f : Sym2 (Fin F.m)) (e0 : Sym2 (Fin n)) (honly : ∀ e ∈ E, crossF F f e → e = e0)
    {x y : Fin n}
    (h : ((SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).deleteEdges {e0}).Reachable x y) :
    (F.T.G.deleteEdges {f}).Reachable (F.ι x) (F.ι y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
    refine Reachable.trans ?_ ih
    rw [deleteEdges_adj, SimpleGraph.fromEdgeSet_adj] at hab
    obtain ⟨⟨habE, _⟩, hne⟩ := hab
    have hnc : ¬ crossF F f s(a, b) := fun hc => hne (by rw [honly _ habE hc]; rfl)
    rw [crossF_mk] at hnc
    push_neg at hnc
    exact hnc

lemma parity (F : SteinerTree (univ : Finset (Fin n))) (E : Finset (Sym2 (Fin n)))
    (hE : (DoublingMST.completeGraph n).IsSpanningTree E) (f : Sym2 (Fin F.m))
    (e0 : Sym2 (Fin n)) (he0 : crossF F f e0) (honly : ∀ e ∈ E, crossF F f e → e = e0)
    (u v : Fin n) (huv : e0 ∈ pathEdges E u v) : crossF F f s(u, v) := by
  classical
  have hn : 0 < n := Fin.pos u
  haveI : Nonempty (Fin n) := ⟨u⟩
  set H := SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n))) with hH
  have hconn : H.Connected := SimpleGraph.Connected.mk (fun a b => by
    obtain ⟨p, hp⟩ := hE.1 a b
    exact reachable_of_walk' E p hp)
  unfold pathEdges at huv
  rw [Finset.mem_filter] at huv
  have hdel : SimpleGraph.fromEdgeSet ((E : Set (Sym2 (Fin n))) \ {e0}) = H.deleteEdges {e0} := by
    rw [hH, SimpleGraph.deleteEdges, SimpleGraph.fromEdgeSet_sdiff]
  rw [hdel] at huv
  obtain ⟨_, hnr⟩ := huv
  induction e0 with
  | _ p q =>
    rw [crossF_mk] at he0 ⊢
    intro hF
    rcases reach_or_reach hconn (a := p) (b := q) u with hu | hu <;>
    rcases reach_or_reach hconn (a := p) (b := q) v with hv | hv
    · exact hnr (hu.trans hv.symm)
    · exact he0 ((side_const F E _ _ honly hu).symm.trans (hF.trans (side_const F E _ _ honly hv)))
    · exact he0 ((side_const F E _ _ honly hv).symm.trans (hF.symm.trans (side_const F E _ _ honly hu)))
    · exact hnr (hu.trans hv.symm)

/-- The core of Lemma 4.3: from a dominated Steiner tree `F` on all points and a spanning tree
`E`, a dominated shortening of `E` of weight at least `w(F) - (w(E) - w(F))`. -/
theorem core (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (F : SteinerTree (univ : Finset (Fin n))) (hF : Dominated d F)
    (E : Finset (Sym2 (Fin n))) (hE : (DoublingMST.completeGraph n).IsSpanningTree E) :
    ∃ w' : Sym2 (Fin n) → ℝ, IsDominatedShortening d E w' ∧
      F.weight - (DoublingMST.treeWeight d E - F.weight) ≤ ∑ e ∈ E, w' e := by
  classical
  set cnt : Sym2 (Fin F.m) → ℕ := fun f => (E.filter (crossF F f)).card with hcnt
  set w' : Sym2 (Fin n) → ℝ := fun e =>
    ∑ f ∈ F.edges, if crossF F f e ∧ cnt f = 1 then F.T.w f else 0 with hw'
  set g : Sym2 (Fin n) → ℝ := fun e => ∑ f ∈ F.edges, if crossF F f e then F.T.w f else 0 with hg
  have hgle : ∀ e, g e ≤ DoublingMST.edgeCost d e := by
    intro e
    induction e with
    | _ u v =>
      rw [edgeCost_mk hd, hg]
      simp only
      rw [← pathWt_eq]
      exact hF u (mem_univ _) v (mem_univ _)
  have hw'le : ∀ e, w' e ≤ g e := by
    intro e
    apply Finset.sum_le_sum
    intro f hf
    by_cases h1 : crossF F f e
    · rw [if_pos h1]
      split_ifs
      · exact le_refl _
      · exact w_nonneg' F hf
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
  have hw'nn : ∀ e, 0 ≤ w' e := by
    intro e
    apply Finset.sum_nonneg
    intro f hf
    split_ifs
    · exact w_nonneg' F hf
    · exact le_refl _
  have hcov : ∀ f ∈ F.edges, 1 ≤ cnt f := by
    intro f hf
    obtain ⟨e, heE, hc⟩ := cover F E hE f ((mem_edges_iff F f).mp hf)
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heE, hc⟩⟩
  -- the swapped sums
  have hsum_g : ∑ e ∈ E, g e = ∑ f ∈ F.edges, (cnt f : ℝ) * F.T.w f := by
    rw [hg]; simp only
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hsum_w' : ∑ e ∈ E, w' e = ∑ f ∈ F.edges, if cnt f = 1 then F.T.w f else 0 := by
    rw [hw']; simp only
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    by_cases h1 : cnt f = 1
    · rw [if_pos h1]
      have : ∀ e, (if crossF F f e ∧ cnt f = 1 then F.T.w f else 0) =
          if crossF F f e then F.T.w f else 0 := fun e => by
        by_cases h2 : crossF F f e
        · rw [if_pos ⟨h2, h1⟩, if_pos h2]
        · rw [if_neg (fun h => h2 h.1), if_neg h2]
      simp only [this]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hc : ((E.filter (crossF F f)).card : ℝ) = 1 := by
        have := h1; simp only [hcnt] at this; exact_mod_cast this
      rw [hc, one_mul]
    · rw [if_neg h1]
      apply Finset.sum_eq_zero
      intro e _
      rw [if_neg (fun h => h1 h.2)]
  have hweight : F.weight = ∑ f ∈ F.edges, F.T.w f := rfl
  have hsplit : ∑ f ∈ F.edges, (cnt f : ℝ) * F.T.w f ≥
      ∑ f ∈ F.edges, F.T.w f + ∑ f ∈ F.edges, (if cnt f = 1 then 0 else F.T.w f) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro f hf
    have h1 := hcov f hf
    have hw := w_nonneg' F hf
    split_ifs with h
    · rw [h]; simp
    · have : (2 : ℝ) ≤ cnt f := by
        have : 2 ≤ cnt f := by omega
        exact_mod_cast this
      nlinarith
  have hEw : ∑ e ∈ E, g e ≤ DoublingMST.treeWeight d E := Finset.sum_le_sum (fun e _ => hgle e)
  have hdecomp : ∑ f ∈ F.edges, F.T.w f = ∑ f ∈ F.edges, (if cnt f = 1 then F.T.w f else 0) +
      ∑ f ∈ F.edges, (if cnt f = 1 then 0 else F.T.w f) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro f _
    split_ifs <;> ring
  refine ⟨w', ⟨fun e _ => ⟨hw'nn e, (hw'le e).trans (hgle e)⟩, ?_⟩, ?_⟩
  · -- domination
    intro u v
    unfold treeDist
    rw [hw']; simp only
    rw [Finset.sum_comm]
    calc ∑ f ∈ F.edges, ∑ e ∈ pathEdges E u v, (if crossF F f e ∧ cnt f = 1 then F.T.w f else 0)
        ≤ ∑ f ∈ F.edges, (if crossF F f s(u, v) then F.T.w f else 0) := by
          apply Finset.sum_le_sum
          intro f hf
          have hw := w_nonneg' F hf
          by_cases h1 : cnt f = 1
          · -- at most one edge of `E` crosses `f`
            obtain ⟨e0, he0⟩ := Finset.card_eq_one.mp (by simpa [hcnt] using h1)
            have hone : ∀ e ∈ E, crossF F f e → e = e0 := fun e heE hc => by
              have : e ∈ E.filter (crossF F f) := Finset.mem_filter.mpr ⟨heE, hc⟩
              rw [he0] at this; exact Finset.mem_singleton.mp this
            have hsub : (pathEdges E u v).filter (fun e => crossF F f e ∧ cnt f = 1) ⊆ {e0} := by
              intro e he
              rw [Finset.mem_filter] at he
              have heE : e ∈ E := (Finset.mem_filter.mp he.1).1
              rw [Finset.mem_singleton]; exact hone e heE he.2.1
            rw [← Finset.sum_filter]
            by_cases hin : e0 ∈ (pathEdges E u v).filter (fun e => crossF F f e ∧ cnt f = 1)
            · have hfe : (pathEdges E u v).filter (fun e => crossF F f e ∧ cnt f = 1) = {e0} :=
                Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hin)
              rw [hfe, Finset.sum_singleton]
              rw [Finset.mem_filter] at hin
              have hcuv := parity F E hE f e0 hin.2.1 hone u v hin.1
              rw [if_pos hcuv]
            · have hfe : (pathEdges E u v).filter (fun e => crossF F f e ∧ cnt f = 1) = ∅ := by
                apply Finset.eq_empty_of_forall_notMem
                intro e he
                have := hsub he
                rw [Finset.mem_singleton] at this
                subst this
                exact hin he
              rw [hfe, Finset.sum_empty]
              split_ifs <;> linarith
          · rw [Finset.sum_eq_zero (fun e _ => if_neg (fun h => h1 h.2))]
            split_ifs <;> linarith
      _ = F.pathWt (F.ι u) (F.ι v) := (pathWt_eq F u v).symm
      _ ≤ d u v := hF u (mem_univ _) v (mem_univ _)
  · rw [hsum_w']
    have := hsum_g
    linarith

end MTSP43



namespace MTSPL43
open MetricTSPSublinear MTSPBridge Finset

theorem mst_treeWeight {n : ℕ} (d : Fin n → Fin n → ℝ) (E : Finset (Sym2 (Fin n)))
    (hE : DoublingMST.IsMSTOf d Finset.univ E) :
    DoublingMST.treeWeight d E = DoublingMST.mstWeight d := by
  apply le_antisymm
  · obtain ⟨E0, hE0, hE0w, _⟩ := exists_mst d
    rw [← hE0w]
    exact hE.2.2 E0 hE0 (Finset.subset_univ _)
  · exact mstWeight_le d E hE.1

theorem lemma_4_3_sol {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (E : Finset (Sym2 (Fin n))) (hE : DoublingMST.IsMSTOf d Finset.univ E) :
    ∃ w' : Sym2 (Fin n) → ℝ, IsDominatedShortening d E w' ∧
      cutLP d Finset.univ - (DoublingMST.mstWeight d - cutLP d Finset.univ) ≤ ∑ e ∈ E, w' e := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨fun _ => 0, ⟨fun e _ => by
      induction e with
      | _ a b => exact a.elim0, fun u _ => u.elim0⟩, ?_⟩
    have hK : cutLP d (univ : Finset (Fin 0)) ≤ 0 := by
      have := cutLP_le hd univ (fun _ => 0) ⟨fun _ => le_refl 0, fun A _ hA _ => by
        obtain ⟨a, _⟩ := hA; exact a.elim0⟩
      simpa using this
    have hM : 0 ≤ DoublingMST.mstWeight d := by
      rw [← mst_treeWeight d E hE]
      exact Finset.sum_nonneg (fun e _ => edgeCost_nonneg hd e)
    simp only [Finset.sum_const_zero]
    linarith
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨y, hy, hyK⟩ := MTSPDual.strong_duality d hd univ
    obtain ⟨F, hF, hFw⟩ := MTSPL42.lemma_4_2_sol d hd univ univ_nonempty y hy
    obtain ⟨w', hw', hbound⟩ := MTSP43.core d hd F hF E hE.1
    refine ⟨w', hw', ?_⟩
    rw [hFw, hyK, mst_treeWeight d E hE] at hbound
    exact hbound

end MTSPL43



open scoped Classical

namespace MTSP44
open Finset MetricTSPSublinear SimpleGraph MTSPBridge

variable {n : ℕ}

lemma reachable_of_walk'' (E : Finset (Sym2 (Fin n))) {u v : Fin n}
    (p : (DoublingMST.completeGraph n).Walk u v) (hp : ∀ e ∈ p.edges, e ∈ E) :
    (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).Reachable u v := by
  induction p with
  | nil => rfl
  | @cons a b c e h p ih =>
    have he : e = s(a, b) := h
    have heF : e ∈ E := hp e (by simp [CombOpt.SpanningTree.Graph.Walk.edges])
    have hrest := ih (fun e' he' => hp e' (by simp [CombOpt.SpanningTree.Graph.Walk.edges, he']))
    refine SimpleGraph.Reachable.trans ?_ hrest
    by_cases hab : a = b
    · rw [hab]
    · apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨by rw [← he]; exact heF, hab⟩

/-- Reachability after deleting `f` from the tree `E`. -/
def Rf (E : Finset (Sym2 (Fin n))) (f : Sym2 (Fin n)) : Fin n → Fin n → Prop :=
  (SimpleGraph.fromEdgeSet ((E : Set (Sym2 (Fin n))) \ {f})).Reachable

lemma Rf_two (E : Finset (Sym2 (Fin n))) (hE : (DoublingMST.completeGraph n).IsSpanningTree E)
    (a b w : Fin n) : Rf E s(a, b) w a ∨ Rf E s(a, b) w b := by
  have hn : 0 < n := Fin.pos w
  haveI : Nonempty (Fin n) := ⟨w⟩
  have hconn : (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).Connected :=
    SimpleGraph.Connected.mk (fun a b => by
      obtain ⟨p, hp⟩ := hE.1 a b
      exact reachable_of_walk'' E p hp)
  have h := MTSPTree.reach_or_reach hconn (a := a) (b := b) w
  have hdel : (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).deleteEdges {s(a, b)} =
      SimpleGraph.fromEdgeSet ((E : Set (Sym2 (Fin n))) \ {s(a, b)}) := by
    rw [SimpleGraph.deleteEdges, SimpleGraph.fromEdgeSet_sdiff]
  rw [hdel] at h
  exact h

/-- Two reachability classes: separation of `p, q` by the side of `x`. -/
lemma Rf_sep (E : Finset (Sym2 (Fin n))) (hE : (DoublingMST.completeGraph n).IsSpanningTree E)
    (f : Sym2 (Fin n)) (u0 v0 : Fin n) (h0 : ¬ Rf E f u0 v0) (x p q : Fin n) :
    ((Rf E f x p ↔ Rf E f x q) ↔ Rf E f p q) := by
  induction f with
  | _ a b =>
    set R := Rf E s(a, b) with hR
    have hab : ¬ R a b := by
      intro hab
      have hu := Rf_two E hE a b u0
      have hv := Rf_two E hE a b v0
      apply h0
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact hu.trans hv.symm
      · exact hu.trans (hab.trans hv.symm)
      · exact hu.trans (hab.symm.trans hv.symm)
      · exact hu.trans hv.symm
    have hx := Rf_two E hE a b x
    have hp := Rf_two E hE a b p
    have hq := Rf_two E hE a b q
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

/-- Lower bound of Lemma 4.4, given a dominated shortening `w'` of `E`. -/
theorem hull_lb (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (E : Finset (Sym2 (Fin n))) (hE : (DoublingMST.completeGraph n).IsSpanningTree E)
    (w' : Sym2 (Fin n) → ℝ) (hw' : IsDominatedShortening d E w') (S : Finset (Fin n)) :
    DoublingMST.treeWeight d (hull E S) - (DoublingMST.treeWeight d E - ∑ e ∈ E, w' e) ≤
      cutLP d S := by
  have hhullE : hull E S ⊆ E := Finset.filter_subset _ _
  have hloss : DoublingMST.treeWeight d (hull E S) - ∑ f ∈ hull E S, w' f ≤
      DoublingMST.treeWeight d E - ∑ e ∈ E, w' e := by
    unfold DoublingMST.treeWeight
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum_of_subset_of_nonneg hhullE
    intro e he _
    have := (hw'.1 e he).2
    linarith
  suffices hmain : ∑ f ∈ hull E S, w' f ≤ cutLP d S by linarith
  rcases S.eq_empty_or_nonempty with hS | ⟨x₀, hx₀⟩
  · subst hS
    have : hull E ∅ = ∅ := by
      unfold hull; apply Finset.filter_false_of_mem; intro e _; simp
    rw [this, Finset.sum_empty]
    exact le_cutLP ∅ 0 (fun x hx => cutLP_obj_nonneg hd ∅ x hx)
  -- the dual solution of the shortened hull
  set side : Sym2 (Fin n) → Finset (Fin n) := fun f => S.filter (fun v => ¬ Rf E f x₀ v) with hside
  set y : Finset (Fin n) → ℝ := fun A => ∑ f ∈ hull E S, if side f = A then w' f else 0 with hy
  have hmemhull : ∀ f ∈ hull E S, f ∈ E ∧ ∃ u ∈ S, ∃ v ∈ S, ¬ Rf E f u v := by
    intro f hf
    unfold hull at hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hfE, u, hu, v, hv, hpe⟩ := hf
    unfold pathEdges at hpe
    exact ⟨hfE, u, hu, v, hv, (Finset.mem_filter.mp hpe).2⟩
  have hsepiff : ∀ f ∈ hull E S, ∀ u ∈ S, ∀ v ∈ S,
      (¬ ((u ∈ side f) ↔ (v ∈ side f)) ↔ f ∈ pathEdges E u v) := by
    intro f hf u hu v hv
    obtain ⟨hfE, u0, _, v0, _, h0⟩ := hmemhull f hf
    have h := Rf_sep E hE f u0 v0 h0 x₀ u v
    unfold pathEdges
    rw [Finset.mem_filter]
    simp only [hside, Finset.mem_filter, hu, hv, true_and]
    unfold Rf at h
    constructor
    · intro hn; exact ⟨hfE, fun hr => hn (by tauto)⟩
    · intro hn; have := hn.2; tauto
  have hfeas : IsDualFeasible d S y := by
    refine ⟨?_, ?_, ?_⟩
    · intro A
      apply Finset.sum_nonneg
      intro f hf
      split_ifs
      · exact (hw'.1 f (hhullE hf)).1
      · exact le_refl _
    · intro A hA
      apply Finset.sum_eq_zero
      intro f hf
      rw [if_neg]
      intro hfA
      apply hA
      subst hfA
      obtain ⟨_, u, hu, v, hv, huv⟩ := hmemhull f hf
      refine ⟨Finset.filter_subset _ _, ?_, ?_⟩
      · by_cases hxu : Rf E f x₀ u
        · refine ⟨v, Finset.mem_filter.mpr ⟨hv, fun hxv => huv (hxu.symm.trans hxv)⟩⟩
        · exact ⟨u, Finset.mem_filter.mpr ⟨hu, hxu⟩⟩
      · intro hS
        have : x₀ ∈ side f := by rw [hS]; exact hx₀
        exact (Finset.mem_filter.mp this).2 (Reachable.refl _)
    · intro u hu v hv _
      have hsub : pathEdges E u v ⊆ hull E S := by
        intro f hf
        unfold hull
        rw [Finset.mem_filter]
        exact ⟨Finset.filter_subset _ _ hf, u, hu, v, hv, hf⟩
      have hsum : ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => ¬ ((u ∈ A) ↔ (v ∈ A))), y A
          = ∑ f ∈ pathEdges E u v, w' f := by
        rw [hy]
        simp only
        rw [Finset.sum_comm]
        calc ∑ f ∈ hull E S, ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => ¬ ((u ∈ A) ↔ (v ∈ A))),
              (if side f = A then w' f else 0)
            = ∑ f ∈ hull E S, (if f ∈ pathEdges E u v then w' f else 0) := by
              apply Finset.sum_congr rfl
              intro f hf
              rw [Finset.sum_ite_eq]
              apply if_congr _ rfl rfl
              rw [Finset.mem_filter]
              simp only [Finset.mem_univ, true_and]
              exact hsepiff f hf u hu v hv
          _ = ∑ f ∈ pathEdges E u v, w' f := by
              rw [← Finset.sum_filter]
              congr 1
              ext f
              rw [Finset.mem_filter]
              exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
      rw [hsum]
      exact hw'.2 u v
  have htot : ∑ A, y A = ∑ f ∈ hull E S, w' f := by
    rw [hy]; simp only
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.sum_ite_eq]
    simp
  rw [← htot]
  exact MTSPDual.weak_duality d hd S y hfeas

end MTSP44



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



open scoped Classical

namespace MTSPHull
open Finset

/-! ### Lists: path cost, consecutive pairs, shortcutting -/

section Lists
variable {α : Type*}

/-- Path cost of a list. -/
noncomputable def pc (c : α → α → ℝ) : List α → ℝ
  | a :: b :: t => c a b + pc c (b :: t)
  | _ => 0

/-- Consecutive pairs of a list. -/
def pe : List α → List (Sym2 α)
  | a :: b :: t => s(a, b) :: pe (b :: t)
  | _ => []

lemma pc_cons_le (c : α → α → ℝ) (htri : ∀ x y z, c x z ≤ c x y + c y z) (a b : α)
    (r : List α) (hr : r ≠ []) : pc c (a :: r) ≤ c a b + pc c (b :: r) := by
  cases r with
  | nil => exact absurd rfl hr
  | cons x r => simp only [pc]; linarith [htri a b x]

lemma shortcut (c : α → α → ℝ) (htri : ∀ x y z, c x z ≤ c x y + c y z) (p : α → Bool) (z : α) :
    ∀ (l : List α) (a : α), pc c (a :: (l.filter p ++ [z])) ≤ pc c (a :: (l ++ [z])) := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons b t ih =>
    intro a
    by_cases hb : p b = true
    · rw [List.filter_cons_of_pos hb]
      have := ih b
      simp only [List.cons_append, pc] at this ⊢
      linarith
    · rw [List.filter_cons_of_neg hb]
      have h1 := pc_cons_le c htri a b (t ++ [z]) (by simp)
      have h2 := ih a
      simp only [List.cons_append, pc] at h1 h2 ⊢
      linarith

lemma pe_append (l1 : List α) (b : α) (l2 : List α) :
    pe (l1 ++ b :: l2) = pe (l1 ++ [b]) ++ pe (b :: l2) := by
  induction l1 with
  | nil => simp [pe]
  | cons a t ih =>
    cases t with
    | nil => simp [pe]
    | cons a' t' =>
      simp only [List.cons_append] at ih ⊢
      simp only [pe, ih, List.cons_append]

lemma ex_cross (C : Finset (Sym2 α)) (P Q : α → Prop)
    (hC : ∀ x y, P x → P y → Q x → ¬ Q y → s(x, y) ∈ C) :
    ∀ (t : List α) (a z : α), (∀ x ∈ a :: (t ++ [z]), P x) → Q a → ¬ Q z →
      ∃ f ∈ pe (a :: (t ++ [z])), f ∈ C := by
  intro t
  induction t with
  | nil =>
    intro a z hP ha hz
    refine ⟨s(a, z), by simp [pe], hC a z (hP a (by simp)) (hP z (by simp)) ha hz⟩
  | cons b t ih =>
    intro a z hP ha hz
    by_cases hb : Q b
    · obtain ⟨f, hf, hfC⟩ := ih b z (fun x hx => hP x (by simp at hx ⊢; tauto)) hb hz
      refine ⟨f, ?_, hfC⟩
      simp only [List.cons_append, pe] at hf ⊢
      exact List.mem_cons_of_mem _ hf
    · refine ⟨s(a, b), ?_, hC a b (hP a (by simp)) (hP b (by simp)) ha hb⟩
      simp [pe]

/-- Half the number of occurrences of `e` among the pairs `l`. -/
noncomputable def xl (l : List (Sym2 α)) (e : Sym2 α) : ℝ :=
  (1 / 2 : ℝ) * (l.map (fun f => if f = e then (1 : ℝ) else 0)).sum

lemma xl_nonneg (l : List (Sym2 α)) (e : Sym2 α) : 0 ≤ xl l e := by
  unfold xl
  apply mul_nonneg (by norm_num)
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨f, _, rfl⟩ := hx
  split_ifs <;> norm_num

lemma sum_xl (F : Finset (Sym2 α)) (g : Sym2 α → ℝ) :
    ∀ l : List (Sym2 α), ∑ e ∈ F, g e * xl l e
      = (1 / 2 : ℝ) * (l.map (fun f => if f ∈ F then g f else 0)).sum := by
  intro l
  induction l with
  | nil => simp [xl]
  | cons f t ih =>
    unfold xl at ih ⊢
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]
    congr 1
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs <;> ring

lemma one_le_sum_ind (C : Finset (Sym2 α)) (l : List (Sym2 α)) (f : Sym2 α) (hf : f ∈ l)
    (hfC : f ∈ C) : 1 ≤ (l.map (fun f => if f ∈ C then (1 : ℝ) else 0)).sum := by
  have h := List.single_le_sum (l := l.map (fun f => if f ∈ C then (1 : ℝ) else 0))
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨f, _, rfl⟩ := hx; split_ifs <;> norm_num)
    (if f ∈ C then (1 : ℝ) else 0) (List.mem_map.mpr ⟨f, hf, rfl⟩)
  simpa [hfC] using h

lemma pc_congr (c c' : α → α → ℝ) (P : α → Prop) (h : ∀ x y, P x → P y → c x y = c' x y) :
    ∀ l : List α, (∀ x ∈ l, P x) → pc c l = pc c' l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro hP
    cases t with
    | nil => rfl
    | cons b t =>
      simp only [pc]
      rw [h a b (hP a (by simp)) (hP b (by simp)), ih (fun x hx => hP x (List.mem_cons_of_mem _ hx))]

end Lists

/-! ### Tours as lists -/

lemma pc_ofFn {α : Type*} (c : α → α → ℝ) :
    ∀ (m : ℕ) (f : Fin (m + 1) → α) (z : α),
      pc c (List.ofFn f ++ [z]) = ∑ i : Fin m, c (f i.castSucc) (f i.succ) + c (f (Fin.last m)) z := by
  intro m
  induction m with
  | zero => intro f z; simp [pc]
  | succ m ih =>
    intro f z
    have h1 : List.ofFn f = f 0 :: List.ofFn (fun i : Fin (m + 1) => f i.succ) := List.ofFn_succ
    have h2 : List.ofFn (fun i : Fin (m + 1) => f i.succ)
        = f (0 : Fin (m + 1)).succ :: List.ofFn (fun i : Fin m => f i.succ.succ) := List.ofFn_succ
    have hih := ih (fun i : Fin (m + 1) => f i.succ) z
    rw [h2] at hih
    rw [h1, h2]
    simp only [List.cons_append, pc] at hih ⊢
    rw [hih, Fin.sum_univ_succ]
    simp only [Fin.succ_castSucc, Fin.castSucc_zero, Fin.succ_last]
    ring

lemma tourCost_eq_pc {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ) (π : Equiv.Perm (Fin (m + 1))) :
    MetricTSP.tourCost c π = pc c (List.ofFn π ++ [π 0]) := by
  rw [pc_ofFn c m π (π 0), MetricTSP.tourCost, Fin.sum_univ_castSucc, finRotate_last]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [finRotate_apply, Fin.coeSucc_eq_succ]

lemma tourCost_rot {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ) (π : Equiv.Perm (Fin (m + 1)))
    (k : ℕ) : MetricTSP.tourCost c (π * (finRotate (m + 1)) ^ k) = MetricTSP.tourCost c π := by
  unfold MetricTSP.tourCost
  have hcomm : ∀ i, ((finRotate (m + 1)) ^ k) (finRotate (m + 1) i)
      = finRotate (m + 1) (((finRotate (m + 1)) ^ k) i) := by
    intro i
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, pow_mul_comm']
  simp only [Equiv.Perm.mul_apply, hcomm]
  exact Equiv.sum_comp ((finRotate (m + 1)) ^ k) (fun j => c (π j) (π (finRotate (m + 1) j)))

/-- Shortcutting a tour to `S`. -/
lemma tour_shortcut {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ)
    (htri : ∀ x y z, c x z ≤ c x y + c y z) (π : Equiv.Perm (Fin (m + 1)))
    (S : Finset (Fin (m + 1))) (s0 : Fin (m + 1)) (hs0 : s0 ∈ S) :
    ∃ (h : Fin (m + 1)) (M : List (Fin (m + 1))), h ∈ S ∧ (∀ x ∈ M, x ∈ S) ∧
      (∀ x ∈ S, x = h ∨ x ∈ M) ∧ pc c (h :: (M ++ [h])) ≤ MetricTSP.tourCost c π := by
  set j := π.symm s0
  set π' := π * (finRotate (m + 1)) ^ j.val with hπ'
  have h0 : π' 0 = s0 := by
    rw [hπ', Equiv.Perm.mul_apply, Equiv.Perm.coe_pow]
    have : (finRotate (m + 1))^[j.val] 0 = j := by
      apply Fin.ext
      rw [MTSPBridge.finRotate_iter_val]
      simp [Nat.mod_eq_of_lt j.isLt]
    rw [this]; simp [j]
  set R := List.ofFn (fun i : Fin m => π' i.succ)
  refine ⟨s0, R.filter (fun x => decide (x ∈ S)), hs0, ?_, ?_, ?_⟩
  · intro x hx; simpa using (List.mem_filter.mp hx).2
  · intro x _
    by_cases hx : x = s0
    · exact Or.inl hx
    · right
      rw [List.mem_filter]
      refine ⟨?_, by simpa⟩
      obtain ⟨i, hi⟩ := π'.surjective x
      have hi0 : i ≠ 0 := by rintro rfl; exact hx (hi ▸ h0)
      obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi0
      rw [List.mem_ofFn]
      exact ⟨i', hi⟩
  · rw [← tourCost_rot c π j.val, ← hπ', tourCost_eq_pc, List.ofFn_succ, h0]
    have := shortcut c htri (fun x => decide (x ∈ S)) s0 R s0
    simpa [R] using this

/-! ### The cut LP point of a closed sequence -/

lemma pc_eq_sum_pe {n : ℕ} {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) :
    ∀ l : List (Fin n), pc d l = ((pe l).map (DoublingMST.edgeCost d)).sum := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => simp [pc, pe]
    | cons b t =>
      simp only [pc, pe, List.map_cons, List.sum_cons, MTSPBridge.edgeCost_mk hd] at ih ⊢
      rw [ih]

lemma obj_le {n : ℕ} {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d) (S : Finset (Fin n))
    (K : List (Fin n)) :
    ∑ e ∈ MetricTSPSublinear.pairsIn S, DoublingMST.edgeCost d e * xl (pe K) e ≤ (1 / 2) * pc d K := by
  rw [sum_xl, pc_eq_sum_pe hd]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply List.sum_le_sum
  intro f _
  split_ifs
  · exact le_refl _
  · exact MTSPBridge.edgeCost_nonneg hd f

lemma feasible_of_cycle {n : ℕ} (S : Finset (Fin n)) (h : Fin n) (M : List (Fin n)) (hh : h ∈ S)
    (hM : ∀ x ∈ M, x ∈ S) (hcov : ∀ x ∈ S, x = h ∨ x ∈ M) :
    MetricTSPSublinear.IsCutFeasible S (xl (pe (h :: (M ++ [h])))) := by
  refine ⟨xl_nonneg _, ?_⟩
  intro A hAS hAne hAneS
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hbS, hbA⟩ : ∃ b ∈ S, b ∉ A := by
    by_contra hc; push Not at hc; exact hAneS (Finset.Subset.antisymm hAS hc)
  obtain ⟨y, hyM, hy⟩ : ∃ y ∈ M, (h ∈ A ↔ y ∉ A) := by
    by_cases hhA : h ∈ A
    · rcases hcov b hbS with rfl | hb
      · exact absurd hhA hbA
      · exact ⟨b, hb, by tauto⟩
    · rcases hcov a (hAS ha) with rfl | ha'
      · exact absurd ha hhA
      · exact ⟨a, ha', by tauto⟩
  have hcut : ∀ x z, x ∈ S → z ∈ S → (x ∈ A ↔ z ∉ A) →
      s(x, z) ∈ MetricTSPSublinear.cutEdges S A := by
    intro x z hx hz hxz
    unfold MetricTSPSublinear.cutEdges
    by_cases hxA : x ∈ A
    · exact Finset.mem_image.mpr ⟨(x, z), Finset.mem_product.mpr
        ⟨hxA, Finset.mem_sdiff.mpr ⟨hz, hxz.mp hxA⟩⟩, rfl⟩
    · have hzA : z ∈ A := by tauto
      exact Finset.mem_image.mpr ⟨(z, x), Finset.mem_product.mpr
        ⟨hzA, Finset.mem_sdiff.mpr ⟨hx, hxA⟩⟩, Sym2.eq_swap⟩
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hyM
  have hsplit : h :: (s ++ y :: t ++ [h]) = (h :: s) ++ y :: (t ++ [h]) := by simp
  have hpe := pe_append (h :: s) y (t ++ [h])
  rw [← hsplit] at hpe
  simp only [List.cons_append] at hpe
  set C := MetricTSPSublinear.cutEdges S A with hCdef
  have hC1 : ∀ x z, x ∈ S → z ∈ S → (x ∈ A ↔ h ∈ A) → ¬ (z ∈ A ↔ h ∈ A) → s(x, z) ∈ C := by
    intro x z hx hz h1 h2; exact hcut x z hx hz (by tauto)
  have hC2 : ∀ x z, x ∈ S → z ∈ S → ¬ (x ∈ A ↔ h ∈ A) → ¬ ¬ (z ∈ A ↔ h ∈ A) → s(x, z) ∈ C := by
    intro x z hx hz h1 h2; exact hcut x z hx hz (by tauto)
  have hyS : y ∈ S := hM y (by simp)
  obtain ⟨f1, hf1, hf1C⟩ := ex_cross C (· ∈ S) (fun x => x ∈ A ↔ h ∈ A) hC1 s h y
    (by
      intro x hx
      simp at hx
      rcases hx with rfl | hx | rfl
      · exact hh
      · exact hM x (by simp [hx])
      · exact hyS)
    (by simp) (by tauto)
  obtain ⟨f2, hf2, hf2C⟩ := ex_cross C (· ∈ S) (fun x => ¬ (x ∈ A ↔ h ∈ A)) hC2 t y h
    (by
      intro x hx
      simp at hx
      rcases hx with rfl | hx | rfl
      · exact hyS
      · exact hM x (by simp [hx])
      · exact hh)
    (by tauto) (by simp)
  have hsum := sum_xl C (fun _ => (1 : ℝ)) (pe (h :: (s ++ y :: t ++ [h])))
  simp only [one_mul] at hsum
  rw [hsum, hpe, List.map_append, List.sum_append]
  have h1 := one_le_sum_ind C _ f1 hf1 hf1C
  have h2 := one_le_sum_ind C _ f2 hf2 hf2C
  linarith

/-! ### The tree -/

section Tree
variable {n : ℕ}
open SimpleGraph

lemma reachable_of_walk (F : Finset (Sym2 (Fin n))) {u v : Fin n}
    (p : (DoublingMST.completeGraph n).Walk u v) (hp : ∀ e ∈ p.edges, e ∈ F) :
    (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).Reachable u v := by
  induction p with
  | nil => rfl
  | @cons a b c e h p ih =>
    have he : e = s(a, b) := h
    have heF : e ∈ F := hp e (by simp [CombOpt.SpanningTree.Graph.Walk.edges])
    have hrest := ih (fun e' he' => hp e' (by simp [CombOpt.SpanningTree.Graph.Walk.edges, he']))
    refine SimpleGraph.Reachable.trans ?_ hrest
    by_cases hab : a = b
    · rw [hab]
    · apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨by rw [← he]; exact heF, hab⟩

lemma ofWalk_support {G : SimpleGraph (Fin n)} {u v : Fin n} (p : G.Walk u v) :
    (MTSPBridge.ofWalk p).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [MTSPBridge.ofWalk, CombOpt.SpanningTree.Graph.Walk.support, Walk.support_cons, ih]

lemma isTree_of {E : Finset (Sym2 (Fin n))}
    (hE : (DoublingMST.completeGraph n).IsSpanningTree E) (hn : 0 < n) :
    (fromEdgeSet (E : Set (Sym2 (Fin n)))).IsTree := by
  refine ⟨?_, ?_⟩
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Connected.mk (fun u v => by
      obtain ⟨p, hp⟩ := hE.1 u v
      exact reachable_of_walk E p hp)
  · intro v c hc
    apply hE.2
    refine ⟨v, MTSPBridge.ofWalk c, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [MTSPBridge.ofWalk_edges]; exact hc.edges_nodup
    · rw [ofWalk_support]; exact hc.nodup_dropLast_support
    · rw [MTSPBridge.ofWalk_edges, Walk.length_edges]; have := hc.three_le_length; omega
    · intro e he
      rw [MTSPBridge.ofWalk_edges] at he
      have := c.edges_subset_edgeSet he
      rw [edgeSet_fromEdgeSet] at this
      exact this.1

lemma deleteEdges_fromEdgeSet' (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    (fromEdgeSet (E : Set (Sym2 (Fin n)))).deleteEdges {e}
      = fromEdgeSet ((E : Set (Sym2 (Fin n))) \ {e}) := by
  ext a b
  simp only [deleteEdges_adj, fromEdgeSet_adj, Set.mem_sdiff, Set.mem_singleton_iff]
  tauto

lemma reach_support {G : SimpleGraph (Fin n)} (F : Set (Sym2 (Fin n))) {u v : Fin n}
    (p : G.Walk u v) (hp : ∀ e ∈ p.edges, e ∈ F) :
    ∀ x ∈ p.support, (fromEdgeSet F).Reachable u x := by
  induction p with
  | nil => intro x hx; simp at hx; subst hx; rfl
  | @cons a b c h p ih =>
    intro x hx
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · have hab : (fromEdgeSet F).Adj a b := by
        rw [fromEdgeSet_adj]; exact ⟨hp _ (by simp), h.ne⟩
      exact hab.reachable.trans (ih (fun e he => hp e (by simp [he])) x hx)

lemma hull_path {E : Finset (Sym2 (Fin n))} (hT : (fromEdgeSet (E : Set (Sym2 (Fin n)))).IsTree)
    (S : Finset (Fin n)) {u u' : Fin n} (hu : u ∈ S) (hu' : u' ∈ S) :
    ∃ p : (fromEdgeSet (E : Set (Sym2 (Fin n)))).Walk u u', p.IsPath ∧
      (∀ e ∈ p.edges, e ∈ MetricTSPSublinear.hull E S) ∧
      (∀ e ∈ MetricTSPSublinear.pathEdges E u u', e ∈ p.edges) := by
  obtain ⟨p, hp⟩ := (hT.existsUnique_path u u').exists
  refine ⟨p, hp, ?_, ?_⟩
  · intro e he
    unfold MetricTSPSublinear.hull
    rw [Finset.mem_filter]
    have heE : e ∈ E := by
      have := p.edges_subset_edgeSet he
      rw [edgeSet_fromEdgeSet] at this
      exact this.1
    refine ⟨heE, u, hu, u', hu', ?_⟩
    unfold MetricTSPSublinear.pathEdges
    rw [Finset.mem_filter, ← deleteEdges_fromEdgeSet']
    exact ⟨heE, (MTSPTree.mem_path_edges_iff hT p hp e).mp he⟩
  · intro e he
    unfold MetricTSPSublinear.pathEdges at he
    rw [Finset.mem_filter, ← deleteEdges_fromEdgeSet'] at he
    exact (MTSPTree.mem_path_edges_iff hT p hp e).mpr he.2

end Tree

open SimpleGraph in
open scoped Classical in
theorem cutLP_le_hull {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (E : Finset (Sym2 (Fin n))) (hE : DoublingMST.IsMSTOf d Finset.univ E) (S : Finset (Fin n)) :
    MetricTSPSublinear.cutLP d S ≤ DoublingMST.treeWeight d (MetricTSPSublinear.hull E S) := by
  have hw0 : 0 ≤ DoublingMST.treeWeight d (MetricTSPSublinear.hull E S) :=
    Finset.sum_nonneg (fun e _ => MTSPBridge.edgeCost_nonneg hd e)
  rcases S.eq_empty_or_nonempty with rfl | ⟨s0, hs0⟩
  · have hx : MetricTSPSublinear.IsCutFeasible (∅ : Finset (Fin n)) (fun _ => 0) :=
      ⟨fun _ => le_refl _, fun A hA ⟨a, ha⟩ _ => absurd (hA ha) (Finset.notMem_empty a)⟩
    have := MTSPBridge.cutLP_le hd ∅ _ hx
    simp only [mul_zero, Finset.sum_const_zero] at this
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := s0.pos; omega⟩
  set H := MetricTSPSublinear.hull E S with hHdef
  have hT := isTree_of hE.1 (Nat.succ_pos m)
  set HV : Finset (Fin (m + 1)) := S ∪ univ.filter (fun v => ∃ e ∈ H, v ∈ e) with hHV
  set r : Fin (m + 1) → Fin (m + 1) := fun v => if v ∈ HV then v else s0 with hr
  set c : Fin (m + 1) → Fin (m + 1) → ℝ := fun a b => d (r a) (r b) with hcdef
  have hc : MetricTSP.IsMetricCost c :=
    ⟨fun u v => hd.2.1 _ _, fun v => (hd.1 _ _).2 rfl, fun u v w => hd.2.2 _ _ _⟩
  have hrS : ∀ v ∈ HV, r v = v := fun v hv => if_pos hv
  have hs0HV : s0 ∈ HV := Finset.mem_union_left _ hs0
  -- reachability inside the hull
  have hreachS : ∀ u ∈ S, (fromEdgeSet (H : Set (Sym2 (Fin (m + 1))))).Reachable s0 u := by
    intro u hu
    obtain ⟨p, _, hpH, _⟩ := hull_path hT S hs0 hu
    exact reach_support _ p hpH u p.end_mem_support
  have hreach : ∀ v ∈ HV, (fromEdgeSet (H : Set (Sym2 (Fin (m + 1))))).Reachable s0 v := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hreachS v hv
    · obtain ⟨e, heH, hve⟩ := (Finset.mem_filter.mp hv).2
      have heH' := heH
      rw [hHdef] at heH'
      unfold MetricTSPSublinear.hull at heH'
      obtain ⟨_, u, hu, u', hu', hpe⟩ := Finset.mem_filter.mp heH'
      obtain ⟨p, _, hpH, hpall⟩ := hull_path hT S hu hu'
      have hep := hpall e hpe
      have hvs : v ∈ p.support := by
        rw [← Sym2.other_spec hve] at hep
        exact p.fst_mem_support_of_mem_edges hep
      exact (hreachS u hu).trans (reach_support _ p hpH v hvs)
  set X : Finset (Sym2 (Fin (m + 1))) := (univ.filter (fun v => v ∉ HV)).image (fun v => s(v, s0))
    with hX
  set G := fromEdgeSet (((H ∪ X : Finset (Sym2 (Fin (m + 1)))) : Set (Sym2 (Fin (m + 1)))))
    with hG
  have hGconn : G.Connected := by
    have hle : fromEdgeSet (H : Set (Sym2 (Fin (m + 1)))) ≤ G := by
      apply fromEdgeSet_mono
      intro e he
      simp only [Finset.coe_union, Set.mem_union]
      exact Or.inl he
    have hrG : ∀ v, G.Reachable s0 v := by
      intro v
      by_cases hv : v ∈ HV
      · exact (hreach v hv).mono hle
      · apply Adj.reachable
        rw [hG, fromEdgeSet_adj]
        refine ⟨?_, fun h => hv (h ▸ hs0HV)⟩
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
        right
        rw [hX, Finset.mem_image]
        exact ⟨v, Finset.mem_filter.mpr ⟨mem_univ _, hv⟩, Sym2.eq_swap⟩
    exact Connected.mk (fun u v => (hrG u).symm.trans (hrG v))
  have hpc0 : ∀ e, 0 ≤ MetricTSP.pairCost c e := by
    intro e
    induction e with
    | _ a b =>
      show 0 ≤ (c a b + c b a) / 2
      have h1 := MTSPBridge.dist_nonneg' hd (r a) (r b)
      have h2 := MTSPBridge.dist_nonneg' hd (r b) (r a)
      simp only [hcdef]
      linarith
  have hGcost : MetricTSP.graphCost c G ≤ DoublingMST.treeWeight d H := by
    unfold MetricTSP.graphCost DoublingMST.treeWeight
    calc _ ≤ ∑ e ∈ H ∪ X, MetricTSP.pairCost c e := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro e he
            obtain ⟨⟨e', he'⟩, _, rfl⟩ := Finset.mem_map.mp he
            rw [hG, edgeSet_fromEdgeSet] at he'
            exact_mod_cast he'.1
          · intro e _ _; exact hpc0 e
      _ = ∑ e ∈ H, MetricTSP.pairCost c e := by
          symm
          apply Finset.sum_subset Finset.subset_union_left
          intro e he heH
          have heX : e ∈ X := by
            rcases Finset.mem_union.mp he with h | h
            · exact absurd h heH
            · exact h
          rw [hX] at heX
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp heX
          show (c v s0 + c s0 v) / 2 = 0
          have hvr : r v = s0 := if_neg (Finset.mem_filter.mp hv).2
          simp only [hcdef, hvr, hrS s0 hs0HV, (hd.1 s0 s0).2 rfl]
          norm_num
      _ = ∑ e ∈ H, DoublingMST.edgeCost d e := by
          apply Finset.sum_congr rfl
          intro e he
          induction e with
          | _ a b =>
            have ha : a ∈ HV := Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨mem_univ _, s(a, b), he, Sym2.mem_mk_left a b⟩)
            have hb : b ∈ HV := Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨mem_univ _, s(a, b), he, Sym2.mem_mk_right a b⟩)
            rw [MTSPBridge.edgeCost_mk hd]
            show (c a b + c b a) / 2 = d a b
            simp only [hcdef, hrS a ha, hrS b hb, hd.2.1 b a]
            ring
  obtain ⟨π, hπ⟩ := MetricTSP.tour_of_connected (m + 1) (by omega) c hc G hGconn
  obtain ⟨h, M, hh, hM, hcov, hpc⟩ := tour_shortcut c hc.2.2 π S s0 hs0
  have hfeas := feasible_of_cycle S h M hh hM hcov
  have hK := MTSPBridge.cutLP_le hd S _ hfeas
  have hobj := obj_le hd S (h :: (M ++ [h]))
  have hall : ∀ x ∈ h :: (M ++ [h]), x ∈ S := by
    intro x hx
    simp at hx
    rcases hx with rfl | hx | rfl
    · exact hh
    · exact hM x hx
    · exact hh
  have hpcd : pc d (h :: (M ++ [h])) = pc c (h :: (M ++ [h])) :=
    pc_congr d c (· ∈ S) (fun x y hx hy => by
      simp only [hcdef, hrS x (Finset.mem_union_left _ hx), hrS y (Finset.mem_union_left _ hy)])
      _ hall
  linarith

end MTSPHull



namespace MTSPL44
open MetricTSPSublinear

theorem lemma_4_4_sol {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (E : Finset (Sym2 (Fin n)))
    (hE : DoublingMST.IsMSTOf d Finset.univ E) (S : Finset (Fin n)) :
    DoublingMST.treeWeight d (hull E S) - 2 * (DoublingMST.mstWeight d - cutLP d Finset.univ) ≤ cutLP d S ∧
      cutLP d S ≤ DoublingMST.treeWeight d (hull E S) := by
  refine ⟨?_, MTSPHull.cutLP_le_hull d hd E hE S⟩
  obtain ⟨w', hw', hb⟩ := MTSPL43.lemma_4_3_sol d hd E hE
  have h := MTSP44.hull_lb d hd E hE.1 w' hw' S
  rw [MTSPL43.mst_treeWeight d E hE] at h
  linarith

end MTSPL44


open MetricTSPSublinear

theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (E : Finset (Sym2 (Fin n)))
    (hE : DoublingMST.IsMSTOf d Finset.univ E) (S : Finset (Fin n)) :
    DoublingMST.treeWeight d (hull E S) - 2 * (DoublingMST.mstWeight d - cutLP d Finset.univ) ≤ cutLP d S ∧
      cutLP d S ≤ DoublingMST.treeWeight d (hull E S) :=
  MTSPL44.lemma_4_4_sol d hd E hE S
