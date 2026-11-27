-- Prove2me | solution 1 for MetricTSPSublinear.claim_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:38:33.0797+00:00
-- url     : https://prove2.me/submissions/f90b8aca-2dde-43b3-9a20-ad881c2d3823

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_cutLP


namespace MTSPAux
open MetricTSP

open Finset SimpleGraph

variable {n : ℕ}

lemma metric_nonneg'' {c : Fin n → Fin n → ℝ} (hc : IsMetricCost c) (u v : Fin n) :
    0 ≤ c u v := by
  obtain ⟨hsym, hdiag, htri⟩ := hc
  have h := htri u v u
  rw [hdiag u, hsym v u] at h
  linarith

lemma pairCost_nonneg' {c : Fin n → Fin n → ℝ} (hc0 : ∀ u v, 0 ≤ c u v)
    (e : Sym2 (Fin n)) : 0 ≤ pairCost c e := by
  induction e with
  | _ u v =>
    show (0 : ℝ) ≤ (c u v + c v u) / 2
    have h1 := hc0 u v
    have h2 := hc0 v u
    linarith

lemma pairCost_mk' {c : Fin n → Fin n → ℝ} (hsym : ∀ u v, c u v = c v u) (u v : Fin n) :
    pairCost c s(u, v) = c u v := by
  show (c u v + c v u) / 2 = c u v
  rw [hsym v u]
  ring

open Classical in
/-- The edge set of a graph as a `Finset`, with a fixed choice of instance. -/
noncomputable def edgeFin (G : SimpleGraph (Fin n)) : Finset (Sym2 (Fin n)) :=
  G.edgeSet.toFinset

lemma mem_edgeFin {G : SimpleGraph (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ edgeFin G ↔ e ∈ G.edgeSet := by
  classical
  unfold edgeFin
  exact Set.mem_toFinset

/-- The cost of a finite set of unordered pairs. -/
noncomputable def fcost (c : Fin n → Fin n → ℝ) (t : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ e ∈ t, pairCost c e

lemma fcost_graphCost (c : Fin n → Fin n → ℝ) (G : SimpleGraph (Fin n)) :
    graphCost c G = fcost c (edgeFin G) := by
  classical
  unfold graphCost fcost
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  rw [Set.mem_toFinset, mem_edgeFin]

/-- A minimum-cost spanning connected subgraph can be taken to be a tree, and it is
at most as expensive as every spanning connected edge set. -/
lemma exists_min_spanning_tree (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc0 : ∀ u v, 0 ≤ c u v) :
    ∃ TT : SimpleGraph (Fin n), TT.IsTree ∧
      ∀ t : Finset (Sym2 (Fin n)), (SimpleGraph.fromEdgeSet (↑t : Set (Sym2 (Fin n)))).Connected →
        fcost c (edgeFin TT) ≤ fcost c t := by
  classical
  have hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  set cand : Finset (Finset (Sym2 (Fin n))) :=
    univ.filter (fun t => (SimpleGraph.fromEdgeSet (↑t : Set (Sym2 (Fin n)))).Connected)
    with hcand
  have hcne : cand.Nonempty := by
    refine ⟨univ, ?_⟩
    rw [hcand, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcoe : ((univ : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))) = Set.univ := by
      simp
    rw [hcoe, SimpleGraph.fromEdgeSet_univ]
    exact SimpleGraph.connected_top
  obtain ⟨t0, ht0, hmin0⟩ := Finset.exists_min_image cand (fcost c) hcne
  rw [hcand, Finset.mem_filter] at ht0
  obtain ⟨TT, hle, hTree⟩ := ht0.2.exists_isTree_le
  refine ⟨TT, hTree, ?_⟩
  intro t hconn
  have htc : t ∈ cand := by
    rw [hcand, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hconn⟩
  have h1 : fcost c (edgeFin TT) ≤ fcost c t0 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      rw [mem_edgeFin] at he
      have hmem := SimpleGraph.edgeSet_mono hle he
      rw [SimpleGraph.edgeSet_fromEdgeSet] at hmem
      simpa using hmem.1
    · intro e _ _
      exact pairCost_nonneg' hc0 e
  exact le_trans h1 (hmin0 t htc)

/-- The graph of all pairs of cost at most `d`. -/
noncomputable def cheapG (c : Fin n → Fin n → ℝ) (d : ℝ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e : Sym2 (Fin n) | pairCost c e ≤ d}

/-- The subgraph of `TT` consisting of its edges of cost at most `d`. -/
noncomputable def cheapT (TT : SimpleGraph (Fin n)) (c : Fin n → Fin n → ℝ) (d : ℝ) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (TT.edgeSet ∩ {e : Sym2 (Fin n) | pairCost c e ≤ d})

lemma cheapT_le (TT : SimpleGraph (Fin n)) (c : Fin n → Fin n → ℝ) (d : ℝ) :
    cheapT TT c d ≤ TT := by
  intro u v h
  rw [cheapT, SimpleGraph.fromEdgeSet_adj] at h
  exact h.1.1

lemma cheapT_le_cheapG (TT : SimpleGraph (Fin n)) (c : Fin n → Fin n → ℝ) (d : ℝ) :
    cheapT TT c d ≤ cheapG c d := by
  intro u v h
  rw [cheapT, SimpleGraph.fromEdgeSet_adj] at h
  rw [cheapG, SimpleGraph.fromEdgeSet_adj]
  exact ⟨h.1.2, h.2⟩

lemma cheapT_le_delete (TT : SimpleGraph (Fin n)) (c : Fin n → Fin n → ℝ) (d : ℝ)
    (f : Sym2 (Fin n)) (hf : d < pairCost c f) :
    cheapT TT c d ≤ TT.deleteEdges {f} := by
  intro u v h
  rw [cheapT, SimpleGraph.fromEdgeSet_adj] at h
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨h.1.1, ?_⟩
  intro hef
  rw [Set.mem_singleton_iff] at hef
  rw [hef] at h
  exact absurd h.1.2 (not_le.mpr hf)

/-- Along a path in `TT` toward `b`, either the start is already connected to `b` in a
subgraph `C ≤ TT`, or there is a first dart leaving the `C`-region of `a`, and the rest
of the path avoids that dart's edge. -/
lemma cross_aux (TT C : SimpleGraph (Fin n)) (a b : Fin n) :
    ∀ (z : Fin n) (W : TT.Walk z b), W.IsPath → C.Reachable a z →
      C.Reachable a b ∨
      ∃ p q : Fin n, TT.Adj p q ∧ C.Reachable a p ∧ ¬C.Reachable a q ∧
        (TT.deleteEdges {s(p, q)}).Reachable q b := by
  intro z W
  induction W with
  | nil =>
      intro _ hz
      exact Or.inl hz
  | @cons z y bb hadj W' ih =>
      intro hpath hz
      by_cases hy : C.Reachable a y
      · exact ih ((SimpleGraph.Walk.cons_isPath_iff hadj W').mp hpath).1 hy
      · refine Or.inr ⟨z, y, hadj, hz, hy, ?_⟩
        have hnotin : s(z, y) ∉ W'.edges := by
          intro hmem
          have hzsup : z ∈ W'.support :=
            SimpleGraph.Walk.fst_mem_support_of_mem_edges W' hmem
          exact ((SimpleGraph.Walk.cons_isPath_iff hadj W').mp hpath).2 hzsup
        refine ⟨SimpleGraph.Walk.toDeleteEdges {s(z, y)} W' ?_⟩
        intro e he
        rw [Set.mem_singleton_iff]
        intro heq
        rw [heq] at he
        exact hnotin he

/-- After deleting one edge `s(p,q)`, every vertex that could reach `zz` can still
reach `zz`, `p`, or `q`. -/
lemma delete_transfer (H : SimpleGraph (Fin n)) (p q : Fin n) :
    ∀ (z zz : Fin n), H.Walk z zz →
      (H.deleteEdges {s(p, q)}).Reachable z zz ∨
      (H.deleteEdges {s(p, q)}).Reachable z p ∨
      (H.deleteEdges {s(p, q)}).Reachable z q := by
  intro z zz W
  induction W with
  | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
  | @cons z y bb hadj W' ih =>
      by_cases hef : s(z, y) = s(p, q)
      · rcases Sym2.eq_iff.mp hef with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl (SimpleGraph.Reachable.refl _))
        · exact Or.inr (Or.inr (SimpleGraph.Reachable.refl _))
      · have hadj' : (H.deleteEdges {s(p, q)}).Adj z y := by
          rw [SimpleGraph.deleteEdges_adj]
          refine ⟨hadj, ?_⟩
          intro hmem
          rw [Set.mem_singleton_iff] at hmem
          exact hef hmem
        rcases ih with h | h | h
        · exact Or.inl (hadj'.reachable.trans h)
        · exact Or.inr (Or.inl (hadj'.reachable.trans h))
        · exact Or.inr (Or.inr (hadj'.reachable.trans h))

/-- **Exchange argument.** In a minimum-cost spanning tree, the endpoints of a cheap
pair are already connected by cheap tree edges. -/
lemma cheap_span_adj (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ) (hc0 : ∀ u v, 0 ≤ c u v)
    (TT : SimpleGraph (Fin n)) (hTree : TT.IsTree)
    (hmin : ∀ t : Finset (Sym2 (Fin n)),
      (SimpleGraph.fromEdgeSet (↑t : Set (Sym2 (Fin n)))).Connected →
      fcost c (edgeFin TT) ≤ fcost c t)
    (d : ℝ) {a b : Fin n} (hab : (cheapG c d).Adj a b) :
    (cheapT TT c d).Reachable a b := by
  classical
  by_contra hnr
  rw [cheapG, SimpleGraph.fromEdgeSet_adj] at hab
  obtain ⟨habc, habne⟩ := hab
  obtain ⟨P, hP⟩ := (hTree.connected.preconnected a b).exists_isPath
  rcases cross_aux TT (cheapT TT c d) a b a P hP (SimpleGraph.Reachable.refl a) with
    hreach | ⟨p, q, hpq, hap, hnaq, hqb⟩
  · exact hnr hreach
  set f : Sym2 (Fin n) := s(p, q) with hf
  have hfexp : d < pairCost c f := by
    by_contra h
    rw [not_lt] at h
    apply hnaq
    refine hap.trans (SimpleGraph.Adj.reachable ?_)
    rw [cheapT, SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨hpq, h⟩, hpq.ne⟩
  have hfT : f ∈ edgeFin TT := by
    rw [mem_edgeFin]
    exact hpq
  have habT : s(a, b) ∉ edgeFin TT := by
    rw [mem_edgeFin]
    intro hmem
    apply hnr
    apply SimpleGraph.Adj.reachable
    rw [cheapT, SimpleGraph.fromEdgeSet_adj]
    exact ⟨Set.mem_inter hmem habc, habne⟩
  set t' : Finset (Sym2 (Fin n)) := insert s(a, b) ((edgeFin TT).erase f) with ht'
  have hDle : TT.deleteEdges {f} ≤ SimpleGraph.fromEdgeSet (↑t' : Set (Sym2 (Fin n))) := by
    intro u v h
    rw [SimpleGraph.deleteEdges_adj] at h
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨?_, h.1.ne⟩
    rw [ht', Finset.coe_insert, Set.mem_insert_iff]
    right
    rw [Finset.mem_coe, Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro heq
      exact h.2 (by rw [heq]; exact Set.mem_singleton f)
    · rw [mem_edgeFin]
      exact h.1
  have habAdj : (SimpleGraph.fromEdgeSet (↑t' : Set (Sym2 (Fin n)))).Adj a b := by
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨?_, habne⟩
    rw [ht', Finset.coe_insert, Set.mem_insert_iff]
    left
    rfl
  have hcheapD : cheapT TT c d ≤ TT.deleteEdges {f} := cheapT_le_delete TT c d f hfexp
  have hap' : (SimpleGraph.fromEdgeSet (↑t' : Set (Sym2 (Fin n)))).Reachable a p :=
    (hap.mono hcheapD).mono hDle
  have hqb' : (SimpleGraph.fromEdgeSet (↑t' : Set (Sym2 (Fin n)))).Reachable q b :=
    hqb.mono hDle
  have hall : ∀ z, (SimpleGraph.fromEdgeSet (↑t' : Set (Sym2 (Fin n)))).Reachable z a := by
    intro z
    obtain ⟨Wz⟩ := hTree.connected.preconnected z a
    rcases delete_transfer TT p q z a Wz with h | h | h
    · exact h.mono hDle
    · exact (h.mono hDle).trans hap'.symm
    · exact (h.mono hDle).trans (hqb'.trans habAdj.symm.reachable)
  have hconn' : (SimpleGraph.fromEdgeSet (↑t' : Set (Sym2 (Fin n)))).Connected := by
    rw [SimpleGraph.connected_iff]
    exact ⟨fun u v => (hall u).trans (hall v).symm, ⟨a⟩⟩
  have hmin' := hmin t' hconn'
  have habE : s(a, b) ∉ (edgeFin TT).erase f :=
    fun h => habT (Finset.mem_of_mem_erase h)
  have hsum : fcost c t' = pairCost c s(a, b) + (fcost c (edgeFin TT) - pairCost c f) := by
    rw [ht']
    unfold fcost
    rw [Finset.sum_insert habE]
    congr 1
    have := Finset.sum_erase_add (edgeFin TT) (pairCost c) hfT
    linarith
  rw [hsum] at hmin'
  have hd : pairCost c s(a, b) ≤ d := habc
  linarith

/-- Full reachability version of the exchange property. -/
lemma cheap_span (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ) (hc0 : ∀ u v, 0 ≤ c u v)
    (TT : SimpleGraph (Fin n)) (hTree : TT.IsTree)
    (hmin : ∀ t : Finset (Sym2 (Fin n)),
      (SimpleGraph.fromEdgeSet (↑t : Set (Sym2 (Fin n)))).Connected →
      fcost c (edgeFin TT) ≤ fcost c t)
    (d : ℝ) :
    ∀ (u v : Fin n), (cheapG c d).Reachable u v → (cheapT TT c d).Reachable u v := by
  have key : ∀ (u v : Fin n), (cheapG c d).Walk u v → (cheapT TT c d).Reachable u v := by
    intro u v W
    induction W with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hadj W' ih =>
        exact (cheap_span_adj hn c hc0 TT hTree hmin d hadj).trans ih
  intro u v h
  obtain ⟨W⟩ := h
  exact key u v W

/-- Deleting a bridge strictly increases the number of connected components. -/
lemma card_comp_lt_of_bridge {H : SimpleGraph (Fin n)} {u v : Fin n}
    (hadj : H.Adj u v) (hbr : H.IsBridge s(u, v)) :
    Nat.card H.ConnectedComponent < Nat.card (H.deleteEdges {s(u, v)}).ConnectedComponent := by
  classical
  have hnreach : ¬ (H.deleteEdges {s(u, v)}).Reachable u v := SimpleGraph.isBridge_iff.mp hbr
  set D := H.deleteEdges {s(u, v)} with hD
  have hle : D ≤ H := SimpleGraph.deleteEdges_le _
  set ψ : D.ConnectedComponent → H.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE hle) with hψ
  have hsurj : Function.Surjective ψ :=
    SimpleGraph.ConnectedComponent.surjective_map_ofLE hle
  have hle_card : Nat.card H.ConnectedComponent ≤ Nat.card D.ConnectedComponent :=
    Nat.card_le_card_of_surjective ψ hsurj
  rcases lt_or_eq_of_le hle_card with h | h
  · exact h
  exfalso
  -- equal cardinalities force ψ bijective, hence injective — contradicting the bridge
  have hbij : Function.Bijective ψ :=
    hsurj.bijective_of_nat_card_le (le_of_eq h.symm)
  have h1 : ψ (D.connectedComponentMk u) = ψ (D.connectedComponentMk v) := by
    rw [hψ]
    rw [SimpleGraph.ConnectedComponent.map_mk, SimpleGraph.ConnectedComponent.map_mk]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj (by exact hadj)
  have h2 := hbij.injective h1
  rw [SimpleGraph.ConnectedComponent.eq] at h2
  exact hnreach h2

/-- Deleting `j` edges of an acyclic graph creates at least `j` new components. -/
lemma comps_ge_of_acyclic (TT : SimpleGraph (Fin n)) (hac : TT.IsAcyclic) :
    ∀ (E : Finset (Sym2 (Fin n))), (↑E : Set (Sym2 (Fin n))) ⊆ TT.edgeSet →
      E.card + Nat.card TT.ConnectedComponent
        ≤ Nat.card (TT.deleteEdges (↑E : Set (Sym2 (Fin n)))).ConnectedComponent := by
  classical
  intro E
  induction E using Finset.induction_on with
  | empty =>
      intro _
      simp [SimpleGraph.deleteEdges_empty]
  | @insert f E hfE ih =>
      intro hsub
      have hEsub : (↑E : Set (Sym2 (Fin n))) ⊆ TT.edgeSet := by
        intro e he
        exact hsub (by simpa using Or.inr he)
      have hfmem : f ∈ TT.edgeSet := hsub (by simp)
      set H := TT.deleteEdges (↑E : Set (Sym2 (Fin n))) with hH
      have hHle : H ≤ TT := SimpleGraph.deleteEdges_le _
      have hHac : H.IsAcyclic := hac.anti hHle
      have hfH : f ∈ H.edgeSet := by
        rw [hH, SimpleGraph.edgeSet_deleteEdges]
        exact ⟨hfmem, by simpa using hfE⟩
      obtain ⟨u, v⟩ := f
      have hbr : H.IsBridge s(u, v) :=
        SimpleGraph.isAcyclic_iff_forall_isBridge.mp hHac hfH
      have hstep := card_comp_lt_of_bridge (by simpa using hfH) hbr
      have hins : TT.deleteEdges (↑(insert s(u, v) E) : Set (Sym2 (Fin n)))
          = H.deleteEdges {s(u, v)} := by
        rw [hH, SimpleGraph.deleteEdges_deleteEdges]
        congr 1
        ext e
        simp [or_comm]
      rw [hins, Finset.card_insert_of_notMem hfE]
      have := ih hEsub
      omega

/-- The chain: expensive tree edges at level `dd` number at most (number of components of
the cheap graph) minus one. -/
lemma tree_expensive_count (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ) (hc0 : ∀ u v, 0 ≤ c u v)
    (TT : SimpleGraph (Fin n)) (hTree : TT.IsTree)
    (hmin : ∀ t : Finset (Sym2 (Fin n)),
      (SimpleGraph.fromEdgeSet (↑t : Set (Sym2 (Fin n)))).Connected →
      fcost c (edgeFin TT) ≤ fcost c t)
    (dd : ℝ) :
    ((edgeFin TT).filter (fun e => dd < pairCost c e)).card + 1
      ≤ Nat.card ((cheapG c dd).ConnectedComponent) := by
  classical
  set E := (edgeFin TT).filter (fun e => dd < pairCost c e) with hE
  have hdel : TT.deleteEdges (↑E : Set (Sym2 (Fin n))) = cheapT TT c dd := by
    ext u v
    rw [SimpleGraph.deleteEdges_adj, cheapT, SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨hadj, hnE⟩
      refine ⟨⟨hadj, ?_⟩, hadj.ne⟩
      by_contra hexp
      apply hnE
      rw [Finset.mem_coe, hE, Finset.mem_filter]
      exact ⟨mem_edgeFin.mpr hadj, lt_of_not_ge hexp⟩
    · rintro ⟨⟨hadj, hcheap⟩, _⟩
      refine ⟨hadj, ?_⟩
      intro hmem
      rw [Finset.mem_coe, hE, Finset.mem_filter] at hmem
      exact absurd hcheap (not_le.mpr hmem.2)
  have hsub : (↑E : Set (Sym2 (Fin n))) ⊆ TT.edgeSet := by
    intro e he
    rw [Finset.mem_coe, hE, Finset.mem_filter, mem_edgeFin] at he
    exact he.1
  have hcomps := comps_ge_of_acyclic TT hTree.isAcyclic E hsub
  rw [hdel] at hcomps
  have hone : Nat.card TT.ConnectedComponent = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨hTree.connected.preconnected.subsingleton_connectedComponent, ?_⟩
    exact ⟨TT.connectedComponentMk ⟨0, by omega⟩⟩
  have hequiv : (cheapT TT c dd).ConnectedComponent ≃ (cheapG c dd).ConnectedComponent :=
    Quot.congrRight (fun a b =>
      ⟨fun h => h.mono (cheapT_le_cheapG TT c dd), cheap_span hn c hc0 TT hTree hmin dd a b⟩)
  have hcard := Nat.card_congr hequiv
  omega

/-- The next value of `D` strictly above `v`, or `v` itself if there is none. -/
noncomputable def nextD (D : Finset ℝ) (v : ℝ) : ℝ :=
  if h : (D.filter (fun d' => v < d')).Nonempty then (D.filter (fun d' => v < d')).min' h else v

lemma nextD_ge (D : Finset ℝ) (v : ℝ) : v ≤ nextD D v := by
  unfold nextD
  split_ifs with h
  · have hmem := Finset.min'_mem _ h
    rw [Finset.mem_filter] at hmem
    exact le_of_lt hmem.2
  · exact le_refl v

/-- Discrete layer-cake: every nonnegative element of `D` is the sum of the gaps of `D`
below it. -/
lemma telescope (D : Finset ℝ) (h0 : (0:ℝ) ∈ D) (hDpos : ∀ d ∈ D, 0 ≤ d) :
    ∀ (N : ℕ) (v : ℝ), v ∈ D → 0 ≤ v → (D.filter (fun dd => dd < v)).card ≤ N →
      v = ∑ dd ∈ D.filter (fun dd => dd < v), (nextD D dd - dd) := by
  classical
  intro N
  induction N with
  | zero =>
      intro v hv hv0 hcard
      have hempty : D.filter (fun dd => dd < v) = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_antisymm hcard (Nat.zero_le _))
      have hv0' : v = 0 := by
        by_contra hne
        have hpos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hne)
        have hin : (0:ℝ) ∈ D.filter (fun dd => dd < v) := Finset.mem_filter.mpr ⟨h0, hpos⟩
        rw [hempty] at hin
        exact Finset.notMem_empty _ hin
      rw [hempty, hv0']
      simp
  | succ N ih =>
      intro v hv hv0 hcard
      by_cases hne : (D.filter (fun dd => dd < v)).Nonempty
      · set M := (D.filter (fun dd => dd < v)).max' hne with hM
        have hMmem := Finset.max'_mem _ hne
        rw [Finset.mem_filter] at hMmem
        obtain ⟨hMD, hMv⟩ := hMmem
        have hM0 : 0 ≤ M := hDpos M hMD
        have hnext : nextD D M = v := by
          have hfne : (D.filter (fun d' => M < d')).Nonempty :=
            ⟨v, Finset.mem_filter.mpr ⟨hv, hMv⟩⟩
          unfold nextD
          rw [dif_pos hfne]
          apply le_antisymm
          · exact Finset.min'_le _ v (Finset.mem_filter.mpr ⟨hv, hMv⟩)
          · apply Finset.le_min'
            intro y hy
            rw [Finset.mem_filter] at hy
            by_contra hyv
            push_neg at hyv
            have hyf : y ∈ D.filter (fun dd => dd < v) := Finset.mem_filter.mpr ⟨hy.1, hyv⟩
            have := Finset.le_max' _ y hyf
            exact absurd hy.2 (not_lt.mpr this)
        have hins : D.filter (fun dd => dd < v) = insert M (D.filter (fun dd => dd < M)) := by
          ext dd
          rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter]
          constructor
          · rintro ⟨hdD, hdv⟩
            by_cases hdM : dd = M
            · exact Or.inl hdM
            · right
              refine ⟨hdD, ?_⟩
              have hle := Finset.le_max' (D.filter (fun dd => dd < v)) dd
                (Finset.mem_filter.mpr ⟨hdD, hdv⟩)
              exact lt_of_le_of_ne hle hdM
          · rintro (rfl | ⟨hdD, hdM⟩)
            · exact ⟨hMD, hMv⟩
            · exact ⟨hdD, lt_trans hdM hMv⟩
        have hMnotin : M ∉ D.filter (fun dd => dd < M) := by
          intro h
          rw [Finset.mem_filter] at h
          exact lt_irrefl M h.2
        have hcard' : (D.filter (fun dd => dd < M)).card ≤ N := by
          have hc2 : (insert M (D.filter (fun dd => dd < M))).card ≤ N + 1 := hins ▸ hcard
          rw [Finset.card_insert_of_notMem hMnotin] at hc2
          omega
        have hMtel := ih M hMD hM0 hcard'
        rw [hins, Finset.sum_insert hMnotin, hnext, ← hMtel]
        ring
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hv0' : v = 0 := by
          by_contra hvne
          have hpos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hvne)
          have hin : (0:ℝ) ∈ D.filter (fun dd => dd < v) := Finset.mem_filter.mpr ⟨h0, hpos⟩
          rw [hne] at hin
          exact Finset.notMem_empty _ hin
        rw [hne, hv0']
        simp


end MTSPAux



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



namespace MTSPAux
open MetricTSP Finset

variable {n : ℕ}

open Classical in
/-- The mass of `x` on the expensive pairs is at least the number of components of the cheap graph. -/
lemma cross_mass (c : Fin n → Fin n → ℝ) (hsym : ∀ u v, c u v = c v u)
    (x : Fin n → Fin n → ℝ) (hxnn : ∀ u v, 0 ≤ x u v)
    (hxcut : ∀ A : Finset (Fin n), A.Nonempty → A ≠ univ → 1 ≤ ∑ u ∈ A, ∑ v ∈ Aᶜ, x u v)
    (dd : ℝ) (hk : 2 ≤ Nat.card ((cheapG c dd).ConnectedComponent)) :
    (Nat.card ((cheapG c dd).ConnectedComponent) : ℝ)
      ≤ ∑ u, ∑ v, (if dd < c u v then x u v else 0) := by
  classical
  letI : Fintype ((cheapG c dd).ConnectedComponent) := Fintype.ofFinite _
  set comp : Fin n → (cheapG c dd).ConnectedComponent :=
    (cheapG c dd).connectedComponentMk with hcomp
  set fib : (cheapG c dd).ConnectedComponent → Finset (Fin n) :=
    fun C => univ.filter (fun v => comp v = C) with hfib
  have hstep1 : ∀ u v : Fin n, (if comp u ≠ comp v then x u v else 0)
      ≤ (if dd < c u v then x u v else 0) := by
    intro u v
    by_cases h : comp u ≠ comp v
    · rw [if_pos h]
      have hlt : dd < c u v := by
        by_contra hle
        push_neg at hle
        apply h
        have huv : u ≠ v := fun e => h (e ▸ rfl)
        have hadj : (cheapG c dd).Adj u v := by
          rw [cheapG, SimpleGraph.fromEdgeSet_adj]
          refine ⟨?_, huv⟩
          rw [Set.mem_setOf_eq, pairCost_mk' hsym]
          exact hle
        exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      rw [if_pos hlt]
    · rw [if_neg h]
      split_ifs
      · exact hxnn u v
      · exact le_refl 0
  have hgroup : ∑ u, ∑ v, (if comp u ≠ comp v then x u v else 0)
      = ∑ C : (cheapG c dd).ConnectedComponent, ∑ u ∈ fib C,
          ∑ v, (if comp u ≠ comp v then x u v else 0) := by
    rw [Finset.sum_fiberwise_of_maps_to (fun u _ => Finset.mem_univ (comp u))]
  have hcomp_cut : ∀ C : (cheapG c dd).ConnectedComponent,
      1 ≤ ∑ u ∈ fib C, ∑ v, (if comp u ≠ comp v then x u v else 0) := by
    intro C
    have hCne : (fib C).Nonempty := by
      obtain ⟨v, rfl⟩ := C.exists_rep
      exact ⟨v, by rw [hfib, Finset.mem_filter]; exact ⟨Finset.mem_univ v, rfl⟩⟩
    have hCproper : fib C ≠ univ := by
      intro hcontra
      obtain ⟨C', hC'⟩ := Fintype.exists_ne_of_one_lt_card
        (by
          rw [← Nat.card_eq_fintype_card]
          omega) C
      obtain ⟨v', rfl⟩ := C'.exists_rep
      have : v' ∈ fib C := hcontra ▸ Finset.mem_univ v'
      rw [hfib, Finset.mem_filter] at this
      exact hC' this.2
    have hc := hxcut (fib C) hCne hCproper
    refine le_trans hc (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro u hu
    rw [hfib, Finset.mem_filter] at hu
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext v
      simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, hfib]
      rw [hu.2]
      exact ⟨fun h => fun e => h e.symm, fun h e => h e.symm⟩
    · intro _ _; rfl
  calc (Nat.card ((cheapG c dd).ConnectedComponent) : ℝ)
      = ∑ _C : (cheapG c dd).ConnectedComponent, (1 : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]; simp
    _ ≤ ∑ C : (cheapG c dd).ConnectedComponent, ∑ u ∈ fib C,
          ∑ v, (if comp u ≠ comp v then x u v else 0) :=
        Finset.sum_le_sum (fun C _ => hcomp_cut C)
    _ = ∑ u, ∑ v, (if comp u ≠ comp v then x u v else 0) := hgroup.symm
    _ ≤ ∑ u, ∑ v, (if dd < c u v then x u v else 0) :=
        Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hstep1 u v))

open Classical in
/-- The minimum spanning tree costs at most `∑_u ∑_v c u v x u v` for every cut-feasible `x`
(cuts at least `1`). -/
theorem tree_le_cut (n : ℕ) (hn1 : 1 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) :
    ∃ TT : SimpleGraph (Fin n), TT.IsTree ∧
      ∀ x : Fin n → Fin n → ℝ, (∀ u v, 0 ≤ x u v) →
        (∀ A : Finset (Fin n), A.Nonempty → A ≠ univ → 1 ≤ ∑ u ∈ A, ∑ v ∈ Aᶜ, x u v) →
        fcost c (edgeFin TT) ≤ ∑ u, ∑ v, c u v * x u v := by
  classical
  have hc0 := metric_nonneg'' hc
  obtain ⟨TT, hTree, hmin⟩ := exists_min_spanning_tree hn1 c hc0
  refine ⟨TT, hTree, ?_⟩
  intro x hxnn hxcut
  set D : Finset ℝ := insert 0 (Finset.image (fun p : Fin n × Fin n => c p.1 p.2) univ)
    with hD
  have h0D : (0:ℝ) ∈ D := Finset.mem_insert_self 0 _
  have hDpos : ∀ dd ∈ D, 0 ≤ dd := by
    intro dd hdd
    rw [hD, Finset.mem_insert] at hdd
    rcases hdd with rfl | hdd
    · exact le_refl 0
    · obtain ⟨pp, _, rfl⟩ := Finset.mem_image.mp hdd
      exact hc0 pp.1 pp.2
  have hcD : ∀ u v : Fin n, c u v ∈ D := fun u v =>
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(u, v), Finset.mem_univ _, rfl⟩)
  have hpairD : ∀ e : Sym2 (Fin n), pairCost c e ∈ D := by
    intro e
    induction e with
    | _ u v =>
        rw [pairCost_mk' hc.1]
        exact hcD u v
  have htree_expand : fcost c (edgeFin TT)
      = ∑ dd ∈ D, (nextD D dd - dd) *
          (((edgeFin TT).filter (fun e => dd < pairCost c e)).card : ℝ) := by
    unfold fcost
    calc ∑ e ∈ edgeFin TT, pairCost c e
        = ∑ e ∈ edgeFin TT,
            ∑ dd ∈ D.filter (fun dd => dd < pairCost c e), (nextD D dd - dd) := by
          apply Finset.sum_congr rfl
          intro e _
          exact telescope D h0D hDpos D.card (pairCost c e) (hpairD e)
            (pairCost_nonneg' hc0 e) (Finset.card_filter_le _ _)
      _ = ∑ e ∈ edgeFin TT, ∑ dd ∈ D,
            (if dd < pairCost c e then nextD D dd - dd else 0) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_filter]
      _ = ∑ dd ∈ D, ∑ e ∈ edgeFin TT,
            (if dd < pairCost c e then nextD D dd - dd else 0) := Finset.sum_comm
      _ = ∑ dd ∈ D, (nextD D dd - dd) *
            (((edgeFin TT).filter (fun e => dd < pairCost c e)).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro dd _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          ring
  have hswap : ∀ (F : Fin n → Fin n → ℝ → ℝ),
      ∑ u, ∑ v, ∑ dd ∈ D, F u v dd = ∑ dd ∈ D, ∑ u, ∑ v, F u v dd := by
    intro F
    calc ∑ u, ∑ v, ∑ dd ∈ D, F u v dd
        = ∑ u, ∑ dd ∈ D, ∑ v, F u v dd :=
          Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = ∑ dd ∈ D, ∑ u, ∑ v, F u v dd := Finset.sum_comm
  have hobj_expand : ∑ u, ∑ v, c u v * x u v
      = ∑ dd ∈ D, (nextD D dd - dd) *
          (∑ u, ∑ v, (if dd < c u v then x u v else 0)) := by
    calc ∑ u, ∑ v, c u v * x u v
        = ∑ u, ∑ v, ∑ dd ∈ D,
            (if dd < c u v then (nextD D dd - dd) * x u v else 0) := by
          apply Finset.sum_congr rfl; intro u _
          apply Finset.sum_congr rfl; intro v _
          have hcv := telescope D h0D hDpos D.card (c u v) (hcD u v) (hc0 u v)
            (Finset.card_filter_le _ _)
          calc c u v * x u v
              = (∑ dd ∈ D.filter (fun dd => dd < c u v), (nextD D dd - dd)) * x u v := by
                rw [← hcv]
            _ = ∑ dd ∈ D.filter (fun dd => dd < c u v), (nextD D dd - dd) * x u v := by
                rw [Finset.sum_mul]
            _ = ∑ dd ∈ D, (if dd < c u v then (nextD D dd - dd) * x u v else 0) := by
                rw [Finset.sum_filter]
      _ = ∑ dd ∈ D, ∑ u, ∑ v,
            (if dd < c u v then (nextD D dd - dd) * x u v else 0) :=
          hswap _
      _ = ∑ dd ∈ D, (nextD D dd - dd) *
            (∑ u, ∑ v, (if dd < c u v then x u v else 0)) := by
          apply Finset.sum_congr rfl
          intro dd _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro u _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro v _
          rw [mul_ite, mul_zero]
  have hperdd : ∀ dd ∈ D, (nextD D dd - dd) *
      (((edgeFin TT).filter (fun e => dd < pairCost c e)).card : ℝ)
      ≤ (nextD D dd - dd) * (∑ u, ∑ v, (if dd < c u v then x u v else 0)) := by
    intro dd hdd
    have hΔ : 0 ≤ nextD D dd - dd := by
      have := nextD_ge D dd
      linarith
    apply mul_le_mul_of_nonneg_left _ hΔ
    set k := Nat.card ((cheapG c dd).ConnectedComponent) with hkdef
    have hcount := tree_expensive_count hn1 c hc0 TT hTree hmin dd
    set Y := ∑ u, ∑ v, (if dd < c u v then x u v else 0) with hYdef
    have hYnn : 0 ≤ Y := by
      rw [hYdef]
      apply Finset.sum_nonneg; intro u _
      apply Finset.sum_nonneg; intro v _
      split_ifs
      · exact hxnn u v
      · exact le_refl 0
    by_cases hk2 : 2 ≤ k
    · have hcm := cross_mass c hc.1 x hxnn hxcut dd hk2
      have hc1 : (((edgeFin TT).filter (fun e => dd < pairCost c e)).card : ℝ) ≤ (k:ℝ) - 1 := by
        have : ((edgeFin TT).filter (fun e => dd < pairCost c e)).card + 1 ≤ k := hcount
        have hcast : (((edgeFin TT).filter (fun e => dd < pairCost c e)).card + 1 : ℝ) ≤ (k:ℝ) := by
          exact_mod_cast this
        push_cast at hcast
        linarith
      rw [← hkdef] at hcm
      linarith
    · have hcount0 : ((edgeFin TT).filter (fun e => dd < pairCost c e)).card = 0 := by
        omega
      rw [hcount0]
      push_cast
      exact hYnn
  calc fcost c (edgeFin TT)
      = ∑ dd ∈ D, (nextD D dd - dd) *
          (((edgeFin TT).filter (fun e => dd < pairCost c e)).card : ℝ) := htree_expand
    _ ≤ ∑ dd ∈ D, (nextD D dd - dd) * (∑ u, ∑ v, (if dd < c u v then x u v else 0)) :=
        Finset.sum_le_sum hperdd
    _ = ∑ u, ∑ v, c u v * x u v := hobj_expand.symm

end MTSPAux



namespace MTSPBridge
open Finset CombOpt.SpanningTree

variable {n : ℕ}

theorem mst_le_two_mul_obj {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d)
    (x : Sym2 (Fin n) → ℝ) (hx : MetricTSPSublinear.IsCutFeasible univ x) :
    DoublingMST.mstWeight d ≤
      2 * ∑ e ∈ MetricTSPSublinear.pairsIn univ, DoublingMST.edgeCost d e * x e := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : DoublingMST.mstWeight d ≤ DoublingMST.treeWeight d ∅ :=
      mstWeight_le d ∅ ⟨fun u => u.elim0, by rintro ⟨v, _⟩; exact v.elim0⟩
    simp [DoublingMST.treeWeight] at h0
    have := MTSPBridge.cutLP_obj_nonneg hd univ x hx
    linarith
  · obtain ⟨TT, hTT, hle⟩ := MTSPAux.tree_le_cut n hn d (isMetricCost_of_isMetric hd)
    have hfeas := hle (fun u v => x s(u, v)) (fun u v => hx.1 _) (by
      intro A hAne hAU
      have := hx.2 A (Finset.subset_univ A) hAne hAU
      rw [cut_sum] at this
      exact this)
    have hM : DoublingMST.mstWeight d ≤ MTSPAux.fcost d (MTSPAux.edgeFin TT) := by
      have h1 := mstWeight_le d _ (isSpanningTree_of_isTree TT hTT)
      refine le_trans h1 (le_of_eq ?_)
      unfold DoublingMST.treeWeight MTSPAux.fcost
      apply Finset.sum_congr
      · ext e; simp [MTSPAux.mem_edgeFin]
      · intro e _; exact (pairCost_eq_edgeCost hd e).symm
    have hds : ∑ u, ∑ v, d u v * x s(u, v)
        = 2 * ∑ e ∈ MetricTSPSublinear.pairsIn univ, DoublingMST.edgeCost d e * x e := by
      rw [← double_sum_sym2 (fun e => DoublingMST.edgeCost d e * x e)
        (fun a => by simp [edgeCost_diag hd])]
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro v _
      rw [edgeCost_mk hd]
    linarith

end MTSPBridge

open MTSPBridge in
theorem claim_3_2_sol {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) :
    DoublingMST.mstWeight d / 2 ≤ MetricTSPSublinear.cutLP d Finset.univ ∧
      MetricTSPSublinear.cutLP d Finset.univ ≤ DoublingMST.mstWeight d := by
  constructor
  · apply le_cutLP
    intro x hx
    have := mst_le_two_mul_obj hd x hx
    linarith
  · obtain ⟨E, hE, hEw, _⟩ := exists_mst d
    rw [← hEw, ← tree_indicator_cost (d := d) E hE]
    exact cutLP_le hd _ _ (tree_indicator_feasible E hE)


open scoped Classical
open MetricTSPSublinear

theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) :
    DoublingMST.mstWeight d / 2 ≤ cutLP d Finset.univ ∧ cutLP d Finset.univ ≤ DoublingMST.mstWeight d :=
  claim_3_2_sol d hd
