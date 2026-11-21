-- Prove2me | solution 1 for LDPSelect.graph_structure
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T13:58:51.788086+00:00
-- url     : https://prove2.me/submissions/f5d19f1d-0f43-4d8f-8037-0b4a365a9348

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-!
# Structure of graphs all of whose connected components are complete multipartite

A finite simple graph has every connected component complete multipartite if and only if it
contains no induced path on four vertices and no induced paw (a triangle with a pendant vertex).
-/

namespace LDPSelect

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The paw graph: the triangle on `1, 2, 3` with a pendant vertex `0` attached to `3`. -/
abbrev pawGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet ({s(1, 2), s(0, 3), s(1, 3), s(2, 3)} : Set (Sym2 (Fin 4)))

lemma pawGraph_adj_12 : pawGraph.Adj 1 2 := by simp [pawGraph, SimpleGraph.fromEdgeSet_adj]
lemma pawGraph_adj_03 : pawGraph.Adj 0 3 := by simp [pawGraph, SimpleGraph.fromEdgeSet_adj]
lemma pawGraph_adj_13 : pawGraph.Adj 1 3 := by simp [pawGraph, SimpleGraph.fromEdgeSet_adj]
lemma pawGraph_adj_23 : pawGraph.Adj 2 3 := by simp [pawGraph, SimpleGraph.fromEdgeSet_adj]
lemma pawGraph_not_adj_01 : ¬ pawGraph.Adj 0 1 := by simp [pawGraph, SimpleGraph.fromEdgeSet_adj]
lemma pawGraph_not_adj_02 : ¬ pawGraph.Adj 0 2 := by simp [pawGraph, SimpleGraph.fromEdgeSet_adj]

/-- A path on four vertices is not complete multipartite. -/
lemma pathGraph_four_not_cmp : ¬ (SimpleGraph.pathGraph 4).IsCompleteMultipartite := by
  intro h
  have h20 : ¬ (SimpleGraph.pathGraph 4).Adj 2 0 := by simp [SimpleGraph.pathGraph_adj]
  have h03 : ¬ (SimpleGraph.pathGraph 4).Adj 0 3 := by simp [SimpleGraph.pathGraph_adj]
  have h23 : (SimpleGraph.pathGraph 4).Adj 2 3 := by simp [SimpleGraph.pathGraph_adj]
  exact (h.trans 2 0 3 h20 h03) h23

/-- The paw is not complete multipartite. -/
lemma pawGraph_not_cmp : ¬ pawGraph.IsCompleteMultipartite := by
  intro h
  have h10 : ¬ pawGraph.Adj 1 0 := fun h' => pawGraph_not_adj_01 h'.symm
  have h02 : ¬ pawGraph.Adj 0 2 := pawGraph_not_adj_02
  have h12 : pawGraph.Adj 1 2 := pawGraph_adj_12
  exact (h.trans 1 0 2 h10 h02) h12

/-- The paw is connected. -/
lemma pawGraph_preconnected : pawGraph.Preconnected := by
  have hto3 : ∀ u : Fin 4, pawGraph.Reachable u 3 := by
    intro u
    fin_cases u
    · exact pawGraph_adj_03.reachable
    · exact pawGraph_adj_13.reachable
    · exact pawGraph_adj_23.reachable
    · exact SimpleGraph.Reachable.rfl
  intro u v
  exact (hto3 u).trans (hto3 v).symm

/-! ## Constructing induced copies -/

/-- Four vertices `a b c d` inducing the path `a - b - c - d` give an induced `P4`. -/
lemma p4Embedding {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hnac : ¬ G.Adj a c) (hnad : ¬ G.Adj a d) (hnbd : ¬ G.Adj b d) :
    Nonempty (SimpleGraph.pathGraph 4 ↪g G) := by
  have hnac' : ¬ G.Adj c a := fun h => hnac h.symm
  have hnad' : ¬ G.Adj d a := fun h => hnad h.symm
  have hnbd' : ¬ G.Adj d b := fun h => hnbd h.symm
  have hiff : ∀ i j : Fin 4, G.Adj (![a, b, c, d] i) (![a, b, c, d] j) ↔
      (SimpleGraph.pathGraph 4).Adj i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [SimpleGraph.pathGraph_adj, hab, hab.symm, hbc, hbc.symm, hcd, hcd.symm,
        hnac, hnac', hnad, hnad', hnbd, hnbd']
  have hinj : Function.Injective (![a, b, c, d] : Fin 4 → V) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  let f : Fin 4 ↪ V := ⟨![a, b, c, d], hinj⟩
  have h : G.comap f = SimpleGraph.pathGraph 4 := by
    ext i j
    simpa [f, SimpleGraph.comap_adj] using hiff i j
  exact ⟨h ▸ SimpleGraph.Embedding.comap f G⟩

/-- A triangle `y z w` with a pendant `x` attached to `w` gives an induced paw. -/
lemma pawEmbedding {x y z w : V} (hyz : G.Adj y z) (hyw : G.Adj y w) (hzw : G.Adj z w)
    (hxw : G.Adj x w) (hxy : ¬ G.Adj x y) (hxz : ¬ G.Adj x z) :
    Nonempty (pawGraph ↪g G) := by
  have hyx : ¬ G.Adj y x := fun h => hxy h.symm
  have hzx : ¬ G.Adj z x := fun h => hxz h.symm
  have hiff : ∀ i j : Fin 4, G.Adj (![x, y, z, w] i) (![x, y, z, w] j) ↔ pawGraph.Adj i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [pawGraph, SimpleGraph.fromEdgeSet_adj, hyz, hyz.symm, hyw, hyw.symm, hzw, hzw.symm,
        hxw, hxw.symm, hxy, hyx, hxz, hzx]
  have hinj : Function.Injective (![x, y, z, w] : Fin 4 → V) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  let f : Fin 4 ↪ V := ⟨![x, y, z, w], hinj⟩
  have h : G.comap f = pawGraph := by
    ext i j
    simpa [f, SimpleGraph.comap_adj] using hiff i j
  exact ⟨h ▸ SimpleGraph.Embedding.comap f G⟩

/-! ## Walks and distances -/

/-- In a shortest walk, vertices at index distance at least two are non-adjacent. -/
lemma not_adj_getVert_of_shortest {u v : V} {p : G.Walk u v} (hp : p.length = G.dist u v)
    {i j : ℕ} (hij : i + 2 ≤ j) (hji : j ≤ p.length) :
    ¬ G.Adj (p.getVert i) (p.getVert j) := by
  intro hadj
  have hij' : i ≤ p.length := by omega
  have hlen : ((p.take i).append (hadj.toWalk.append (p.drop j))).length
      = i + 1 + (p.length - j) := by
    simp only [Walk.length_append, Walk.take_length, Walk.drop_length, hadj.length_toWalk]
    rw [Nat.min_eq_left hij']
    omega
  have hle := dist_le ((p.take i).append (hadj.toWalk.append (p.drop j)))
  rw [hlen, ← hp] at hle
  have hjeq : j + (p.length - j) = p.length := Nat.add_sub_of_le hji
  omega

/-- A shortest walk of length at least three starts with an induced `P4`. -/
lemma p4_of_three_le_length {u v : V} {p : G.Walk u v} (hp : p.length = G.dist u v)
    (hk : 3 ≤ p.length) : Nonempty (SimpleGraph.pathGraph 4 ↪g G) :=
  p4Embedding (a := p.getVert 0) (b := p.getVert 1) (c := p.getVert 2) (d := p.getVert 3)
    (p.adj_getVert_succ (i := 0) (by omega)) (p.adj_getVert_succ (i := 1) (by omega))
    (p.adj_getVert_succ (i := 2) (by omega))
    (not_adj_getVert_of_shortest hp (i := 0) (j := 2) (by omega) (by omega))
    (not_adj_getVert_of_shortest hp (i := 0) (j := 3) (by omega) (by omega))
    (not_adj_getVert_of_shortest hp (i := 1) (j := 3) (by omega) (by omega))

/-- A path `x - w - y - z` whose end vertex `x` is non-adjacent to `y` and `z` yields an
induced `P4` or an induced paw. -/
lemma p4_or_paw_of_common {x y z w : V} (hxw : G.Adj x w) (hwy : G.Adj w y)
    (hyz : G.Adj y z) (hxy : ¬ G.Adj x y) (hxz : ¬ G.Adj x z) :
    Nonempty (SimpleGraph.pathGraph 4 ↪g G) ∨ Nonempty (pawGraph ↪g G) := by
  by_cases hwz : G.Adj w z
  · exact Or.inr (pawEmbedding hyz hwy.symm hwz.symm hxw hxy hxz)
  · exact Or.inl (p4Embedding hxw hwy hyz hxy hxz hwz)

/-! ## Components and complete multipartite graphs -/

/-- A connected graph embedded in `G` whose image lies in one component inherits complete
multipartiteness from that component. -/
lemma cmp_of_embed_of_components {W : Type*} {H : SimpleGraph W} (hH : H.Preconnected)
    (w₀ : W) (hcomp : ∀ C : G.ConnectedComponent, C.toSimpleGraph.IsCompleteMultipartite)
    (e : H ↪g G) : H.IsCompleteMultipartite := by
  let C₀ : G.ConnectedComponent := G.connectedComponentMk (e w₀)
  have hmem : ∀ w : W, e w ∈ C₀ := by
    intro w
    have h1 : e w ∈ C₀.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      show G.connectedComponentMk (e w) = G.connectedComponentMk (e w₀)
      exact SimpleGraph.ConnectedComponent.sound
        (SimpleGraph.Reachable.map e.toHom (hH w w₀))
    exact h1
  let f : W ↪ C₀ :=
    ⟨fun w => ⟨e w, hmem w⟩, fun a b hab => e.injective (congrArg Subtype.val hab)⟩
  have h : C₀.toSimpleGraph.comap f = H := by
    ext a b
    change C₀.toSimpleGraph.Adj ⟨e a, hmem a⟩ ⟨e b, hmem b⟩ ↔ H.Adj a b
    rw [SimpleGraph.ConnectedComponent.toSimpleGraph_adj]
    exact e.map_adj_iff
  exact (hcomp C₀).comap (h ▸ SimpleGraph.Embedding.comap f C₀.toSimpleGraph)

/-- A connected graph with no induced `P4` and no induced paw is complete multipartite. -/
lemma cmp_of_no_p4_no_paw (hconn : G.Connected)
    (hP4 : IsEmpty (SimpleGraph.pathGraph 4 ↪g G)) (hpaw : IsEmpty (pawGraph ↪g G)) :
    G.IsCompleteMultipartite := by
  by_contra h
  obtain ⟨x, y, z, hxyz⟩ := G.exists_isPathGraph3Compl_of_not_isCompleteMultipartite h
  have hxy : ¬ G.Adj x y := hxyz.not_adj_fst
  have hxz : ¬ G.Adj x z := hxyz.not_adj_snd
  have hyz : G.Adj y z := hxyz.adj
  have hneq : x ≠ y := hxyz.ne_fst
  have hd0 : G.dist x y ≠ 0 := by
    intro hd
    rcases (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hd) with h' | h'
    · exact hneq h'
    · exact h' (hconn x y)
  have hd1 : G.dist x y ≠ 1 := fun hd => hxy (SimpleGraph.dist_eq_one_iff_adj.mp hd)
  have hd2 : 2 ≤ G.dist x y := by omega
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
  have hp2 : 2 ≤ p.length := by omega
  by_cases hsmall : p.length = 2
  · have e1 : G.Adj (p.getVert 0) (p.getVert 1) := p.adj_getVert_succ (i := 0) (by omega)
    have e2 : G.Adj (p.getVert 1) (p.getVert 2) := p.adj_getVert_succ (i := 1) (by omega)
    have h0 : p.getVert 0 = x := p.getVert_zero
    have h2 : p.getVert 2 = y := by rw [← hsmall]; exact p.getVert_length
    rw [h0] at e1
    rw [h2] at e2
    rcases p4_or_paw_of_common e1 e2 hyz hxy hxz with h' | h'
    · obtain ⟨e⟩ := h'
      exact hP4.false e
    · obtain ⟨e⟩ := h'
      exact hpaw.false e
  · have h3 : 3 ≤ p.length := by omega
    obtain ⟨e⟩ := p4_of_three_le_length hp h3
    exact hP4.false e

end LDPSelect

open LDPSelect

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (∀ C : G.ConnectedComponent, C.toSimpleGraph.IsCompleteMultipartite) ↔
      IsEmpty (SimpleGraph.pathGraph 4 ↪g G) ∧
      IsEmpty (SimpleGraph.fromEdgeSet ({s(1, 2), s(0, 3), s(1, 3), s(2, 3)} : Set (Sym2 (Fin 4))) ↪g G) := by
  constructor
  · intro hC
    constructor
    · refine ⟨fun e => ?_⟩
      exact pathGraph_four_not_cmp
        (cmp_of_embed_of_components (SimpleGraph.pathGraph_preconnected 4) 0 hC e)
    · refine ⟨fun e => ?_⟩
      exact pawGraph_not_cmp (cmp_of_embed_of_components pawGraph_preconnected 0 hC e)
  · rintro ⟨hP4, hpaw⟩ C
    refine cmp_of_no_p4_no_paw (SimpleGraph.ConnectedComponent.connected_toSimpleGraph C) ?_ ?_
    · refine ⟨fun e => ?_⟩
      exact hP4.false ((SimpleGraph.Embedding.induce C.supp).comp e)
    · refine ⟨fun e => ?_⟩
      exact hpaw.false ((SimpleGraph.Embedding.induce C.supp).comp e)
