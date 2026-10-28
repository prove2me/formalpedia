-- Prove2me | solution 1 for NashWilliams61.TreePacking.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:40:10.063849+00:00
-- url     : https://prove2.me/submissions/9e27d660-bfdd-42b5-a257-e8117b894ba3

import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open NagamochiIbaraki.EdgeConn NashWilliams61.TreePacking

private theorem adj_ends {V E : Type} (ends : E → Sym2 V) (F : Finset E) (u v : V) :
    (edgeGraph ends F).Adj u v ↔ (∃ e ∈ F, ends e = s(u, v)) ∧ u ≠ v := by
  simp only [edgeGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image, Finset.mem_coe]

private theorem forest_injective {V E : Type} [DecidableEq E] (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (T : Finset E) (hT : IsForest ends T) :
    Set.InjOn ends (T : Set E) := by
  intro e he f hf hef
  by_contra hne
  obtain ⟨u, v, hev⟩ : ∃ u v, ends e = s(u, v) := by
    exact Sym2.inductionOn (ends e) (fun u v => ⟨u, v, rfl⟩)
  have huv : u ≠ v := by simpa only [hev, Sym2.mk_isDiag_iff] using hloop e
  apply hT e he u v hev
  exact ((adj_ends ends (T.erase e) u v).mpr
    ⟨⟨f, Finset.mem_erase.mpr ⟨Ne.symm hne, hf⟩, hef.symm.trans hev⟩, huv⟩).reachable

private theorem forest_acyclic {V E : Type} [DecidableEq E] (ends : E → Sym2 V)
    (T : Finset E) (hT : IsForest ends T) : (edgeGraph ends T).IsAcyclic := by
  apply SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr
  intro u v huv
  obtain ⟨⟨e, he, hev⟩, _⟩ := (adj_ends ends T u v).mp huv
  apply SimpleGraph.isBridge_iff.mpr
  intro hr
  apply hT e he u v hev
  apply hr.mono
  intro a b hab
  obtain ⟨hab, hnot⟩ := SimpleGraph.deleteEdges_adj.mp hab
  obtain ⟨⟨f, hf, hfab⟩, hne⟩ := (adj_ends ends T a b).mp hab
  apply (adj_ends ends (T.erase e) a b).mpr
  refine ⟨⟨f, Finset.mem_erase.mpr ⟨?_, hf⟩, hfab⟩, hne⟩
  intro hfe
  subst f
  apply hnot
  exact Set.mem_singleton_iff.mpr (hfab.symm.trans hev)

theorem solution {V E : Type} [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (W : Finset V) (T : Finset E) (hT : IsTreeOn ends W T) :
    T.card + 1 = W.card := by
  classical
  let G := edgeGraph ends T
  let H := G.induce (W : Set V)
  have hAdjW : ∀ u v, G.Adj u v → u ∈ W ∧ v ∈ W := by
    intro u v huv
    obtain ⟨⟨e, he, hev⟩, _⟩ := (adj_ends ends T u v).mp huv
    constructor
    · exact hT.2.1 e he u (by rw [hev]; simp)
    · exact hT.2.1 e he v (by rw [hev]; simp)
  have hsupport : ∀ {u v : V} (p : G.Walk u v), u ∈ W → ∀ x ∈ p.support, x ∈ W := by
    intro u v p
    induction p with
    | @nil u =>
      intro hu x hx
      have hx : x = u := by simpa using hx
      simpa only [hx] using hu
    | @cons u v w hadj p ih =>
      intro hu x hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hu
      · exact ih (hAdjW u v hadj).2 x hx
  have hconnected : H.Connected := by
    letI : Nonempty (W : Set V) := by
      obtain ⟨v, hv⟩ := hT.1
      exact ⟨⟨v, hv⟩⟩
    constructor
    intro u v
    obtain ⟨p⟩ := hT.2.2.2 u u.2 v v.2
    exact ⟨p.induce (W : Set V) (hsupport p u.2)⟩
  have htree : H.IsTree := ⟨hconnected, (forest_acyclic ends T hT.2.2.1).induce _⟩
  let emb : Sym2 (W : Set V) ↪ Sym2 V := (Function.Embedding.subtype (· ∈ (W : Set V))).sym2Map
  have hedges : H.edgeFinset.map emb = T.image ends := by
    ext q
    constructor
    · intro hq
      obtain ⟨p, hp, hpq⟩ := Finset.mem_map.mp hq
      obtain ⟨u, v⟩ := p
      have hadj : G.Adj u.val v.val := by simpa only [SimpleGraph.mem_edgeFinset, H,
        SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] using hp
      obtain ⟨⟨e, he, hev⟩, _⟩ := (adj_ends ends T u.val v.val).mp hadj
      apply Finset.mem_image.mpr
      exact ⟨e, he, hev.trans hpq⟩
    · intro hq
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨u, v, hev⟩ : ∃ u v, ends e = s(u, v) := by
        exact Sym2.inductionOn (ends e) (fun u v => ⟨u, v, rfl⟩)
      have hu : u ∈ W := hT.2.1 e he u (by rw [hev]; simp)
      have hv : v ∈ W := hT.2.1 e he v (by rw [hev]; simp)
      have huv : u ≠ v := by simpa only [hev, Sym2.mk_isDiag_iff] using hloop e
      apply Finset.mem_map.mpr
      refine ⟨s(⟨u, hu⟩, ⟨v, hv⟩), ?_, ?_⟩
      · simp only [SimpleGraph.mem_edgeFinset, H, SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj]
        exact (adj_ends ends T u v).mpr ⟨⟨e, he, hev⟩, huv⟩
      · exact hev.symm
  have hc : H.edgeFinset.card = T.card := by
    rw [← Finset.card_map emb, hedges]
    exact Finset.card_image_of_injOn (forest_injective ends hloop T hT.2.2.1)
  have hcount := htree.card_edgeFinset
  rw [hc] at hcount
  simpa using hcount

#print axioms solution
