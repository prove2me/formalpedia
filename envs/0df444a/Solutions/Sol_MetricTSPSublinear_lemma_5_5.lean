-- Prove2me | solution 1 for MetricTSPSublinear.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:37:32.138075+00:00
-- url     : https://prove2.me/submissions/b5cb20ce-cec5-499c-a2b7-69dd411182d0

import Definitions.Def_DoublingMST_IsMSTOf
import Definitions.Def_DoublingMST_edgeCost
import Definitions.Def_MetricTSPSublinear_IsDominatedShortening
import Definitions.Def_MetricTSPSublinear_hull
import Definitions.Def_MetricTSPSublinear_treeDist
import Definitions.Def_TreeCoverLB_WeightedTree
import Mathlib
import Theorems.Thm_MetricTSPSublinear_lemma_4_4

section ASM0
-- from Solutions.AL.Tree

/-!
# Generic tree lemmas for the core alignment (Lemma 5.5)

Copied from `Solutions/Sol_claim_6_1.lean` (namespace `MTSPGL`) and `Solutions/Sol_claim_9_2.lean`
(namespace `MTSPPK`), renamed into `MTSPAL`.
-/

open scoped Classical

namespace MTSPAL
open SimpleGraph
section TreeLem
variable {V : Type*} {G : SimpleGraph V}
lemma reach_or_reach_aux {a b : V} : ∀ (w t : V), G.Walk w t → t = a →
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
      simp only [Walk.support_concat, List.mem_append, List.mem_singleton,
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
      have hqnil : q = Walk.nil := (Walk.isPath_iff_nil.mp hq).eq_nil
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

/-- A walk between distinct vertices starts with an edge. -/
lemma exists_first_edge : ∀ {a b : V} (W : G.Walk a b), a ≠ b → ∃ z, G.Adj a z ∧ s(a, z) ∈ W.edges
  | _, _, .nil, h => absurd rfl h
  | _, _, .cons h _, _ => ⟨_, h, by simp⟩

end TreeLem

namespace WT
open TreeCoverLB

variable {X : Type*} (T : WeightedTree X)

lemma path_isPath (a b : X) : (T.path a b).IsPath :=
  (T.isTree.existsUnique_path a b).exists.choose_spec

lemma mem_path_edges (a b : X) (e : Sym2 X) :
    e ∈ (T.path a b).edges ↔ ¬ (T.G.deleteEdges {e}).Reachable a b :=
  mem_path_edges_iff T.isTree _ (path_isPath T a b) e

/-- The edges of the tree path lie on every walk with the same ends. -/
lemma path_edges_subset {a b : X} (W : T.G.Walk a b) {e : Sym2 X} (he : e ∈ (T.path a b).edges) :
    e ∈ W.edges := by
  by_contra h
  exact (mem_path_edges T a b e).mp he ⟨W.toDeleteEdge e h⟩

lemma dist_eq_sum [Fintype X] (a b : X) :
    T.dist a b = ∑ e ∈ T.G.edgeFinset, if e ∈ (T.path a b).edges then T.w e else 0 := by
  have hp := path_isPath T a b
  have h1 : T.dist a b = ((T.path a b).edges.map T.w).sum := by
    unfold TreeCoverLB.WeightedTree.dist KServer.walkWeight
    rw [Walk.edges, List.map_map]
    rfl
  rw [h1, ← List.sum_toFinset _ hp.isTrail.edges_nodup, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  simp only [List.mem_toFinset, Finset.mem_filter, mem_edgeFinset]
  exact ⟨fun h => ⟨(T.path a b).edges_subset_edgeSet h, h⟩, fun h => h.2⟩

lemma dist_comm [Fintype X] (a b : X) : T.dist a b = T.dist b a := by
  rw [dist_eq_sum, dist_eq_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp only [mem_path_edges, reachable_comm]

lemma dist_self [Fintype X] (a : X) : T.dist a a = 0 := by
  rw [dist_eq_sum]
  refine Finset.sum_eq_zero (fun e _ => ?_)
  rw [if_neg]
  rw [mem_path_edges]
  exact fun h => h (Reachable.refl _)

/-- Separation by the side of a tree edge = the edge lies on the path. -/
lemma sep_iff (r a b : X) {f : Sym2 X} (hf : f ∈ T.G.edgeSet) :
    ¬ ((¬ (T.G.deleteEdges {f}).Reachable r a) ↔ (¬ (T.G.deleteEdges {f}).Reachable r b)) ↔
      f ∈ (T.path a b).edges := by
  rw [mem_path_edges]
  induction f with
  | _ x y =>
    have := reach_iff_reach T.isTree (show T.G.Adj x y from hf) r a b
    tauto

/-- Each side of a tree edge (the side away from `r`) contains a leaf. -/
lemma exists_leaf_side [Fintype X] (r : X) {f : Sym2 X} (hf : f ∈ T.G.edgeSet) :
    ∃ c, (∀ y₁ y₂, T.G.Adj c y₁ → T.G.Adj c y₂ → y₁ = y₂) ∧
      ¬ (T.G.deleteEdges {f}).Reachable r c := by
  induction f with
  | _ a' b' =>
    have hadj : T.G.Adj a' b' := hf
    have key : ∀ a b : X, T.G.Adj a b → s(a, b) = s(a', b') →
        (T.G.deleteEdges {s(a, b)}).Reachable r a → ∃ c, (∀ y₁ y₂, T.G.Adj c y₁ → T.G.Adj c y₂ → y₁ = y₂) ∧
          ¬ (T.G.deleteEdges {s(a', b')}).Reachable r c := by
      intro a b hab heq hra
      obtain ⟨c, hbc, hleaf⟩ := exists_leaf_behind T.isTree hab
      refine ⟨c, hleaf, fun hrc => ?_⟩
      rw [← heq] at hrc
      exact not_reach_of_adj T.isTree.isAcyclic hab (hra.symm.trans (hrc.trans hbc.symm))
    rcases reach_or_reach T.isTree.connected (a := a') (b := b') r with h | h
    · exact key a' b' hadj rfl h
    · exact key b' a' hadj.symm Sym2.eq_swap (by rw [Sym2.eq_swap]; exact h)

end WT

section SpanTree
open CombOpt.SpanningTree MetricTSPSublinear

variable {n : ℕ}

/-- The Mathlib simple graph of an edge set (loops dropped). -/
noncomputable abbrev grE (F : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))

/- A Mathlib walk as a walk of the complete graph. -/
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

lemma ofWalk_support {G : SimpleGraph (Fin n)} {u v : Fin n} (p : G.Walk u v) :
    (ofWalk p).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [ofWalk, Graph.Walk.support, SimpleGraph.Walk.support_cons, ih]

lemma mem_of_mem_edgeSet {F : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    (h : e ∈ (grE F).edgeSet) : e ∈ F := by
  rw [SimpleGraph.edgeSet_fromEdgeSet] at h
  exact h.1

lemma isAcyclic_of_isForest {F : Finset (Sym2 (Fin n))}
    (hF : (DoublingMST.completeGraph n).IsForest F) : (grE F).IsAcyclic := by
  intro v c hc
  apply hF
  refine ⟨v, ofWalk c, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [ofWalk_edges]; exact hc.edges_nodup
  · rw [ofWalk_support]; exact hc.nodup_dropLast_support
  · rw [ofWalk_edges, SimpleGraph.Walk.length_edges]
    have := hc.three_le_length
    omega
  · intro e he
    rw [ofWalk_edges] at he
    exact mem_of_mem_edgeSet (c.edges_subset_edgeSet he)

lemma reachable_of_spanConnected {F : Finset (Sym2 (Fin n))}
    (hF : (DoublingMST.completeGraph n).SpanConnected F) (u v : Fin n) : (grE F).Reachable u v := by
  obtain ⟨p, hp⟩ := hF u v
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c e h p ih =>
    have h' : e = s(a, b) := h
    have heF : e ∈ F := hp e (by simp [Graph.Walk.edges])
    have hrest := ih (fun e' he' => hp e' (by simp [Graph.Walk.edges, he']))
    by_cases hab : a = b
    · subst hab; exact hrest
    · refine SimpleGraph.Reachable.trans ?_ hrest
      apply SimpleGraph.Adj.reachable
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨by rw [← h']; exact heF, hab⟩

lemma grE_isTree {F : Finset (Sym2 (Fin n))}
    (hF : (DoublingMST.completeGraph n).IsSpanningTree F) [Nonempty (Fin n)] : (grE F).IsTree :=
  ⟨⟨reachable_of_spanConnected hF.1⟩, isAcyclic_of_isForest hF.2⟩

lemma grE_deleteEdges (F : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    (grE F).deleteEdges {e} = SimpleGraph.fromEdgeSet ((F : Set (Sym2 (Fin n))) \ {e}) := by
  ext x y
  simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_sdiff,
    Set.mem_singleton_iff, Finset.mem_coe]
  tauto

/-- For a path `p` of the tree `F`, the separating edges `pathEdges F u v` are the edges of `p`. -/
lemma mem_pathEdges_iff {F : Finset (Sym2 (Fin n))}
    (hF : (DoublingMST.completeGraph n).IsSpanningTree F) {u v : Fin n} (p : (grE F).Walk u v)
    (hp : p.IsPath) (e : Sym2 (Fin n)) : e ∈ pathEdges F u v ↔ e ∈ p.edges := by
  have : Nonempty (Fin n) := ⟨u⟩
  rw [mem_path_edges_iff (grE_isTree hF) p hp, pathEdges, Finset.mem_filter, grE_deleteEdges]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hne
    apply h
    have : SimpleGraph.fromEdgeSet ((F : Set (Sym2 (Fin n))) \ {e}) = grE F := by
      ext x y
      simp only [SimpleGraph.fromEdgeSet_adj, Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe]
      constructor
      · exact fun h => ⟨h.1.1, h.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun h3 => hne (h3 ▸ h1)⟩, h2⟩
    rw [this]
    exact (reachable_of_spanConnected hF.1 u v)

lemma pathEdges_eq_toFinset {F : Finset (Sym2 (Fin n))}
    (hF : (DoublingMST.completeGraph n).IsSpanningTree F) {u v : Fin n} (p : (grE F).Walk u v)
    (hp : p.IsPath) : pathEdges F u v = p.edges.toFinset := by
  ext e
  rw [mem_pathEdges_iff hF p hp, List.mem_toFinset]

end SpanTree

end MTSPAL

end ASM0

section ASM1
-- from Solutions.AL.Paths

/-!
# Core paths `P_e` and their combinatorics

For the core tree `K` on `Fin m` and the map `q : Fin n → Fin m`, `Pk K x y` is the set of edges of
the `x`–`y` path in `K` (as the edges separating `x` from `y`), and `Pe K q s(u, v) = Pk K (q u) (q v)`
is the core path `P_e` of an edge `e = s(u, v)`.
-/

open scoped Classical

namespace MTSPAL
open SimpleGraph TreeCoverLB MetricTSPSublinear

section KSide
variable {m : ℕ}

/-- The edges of the `x`–`y` path of the tree `K`: the edges whose deletion separates `x` from `y`. -/
noncomputable def Pk (K : WeightedTree (Fin m)) (x y : Fin m) : Finset (Sym2 (Fin m)) :=
  K.G.edgeFinset.filter (fun f => ¬ (K.G.deleteEdges {f}).Reachable x y)

variable (K : WeightedTree (Fin m))

lemma mem_Pk {x y : Fin m} {f : Sym2 (Fin m)} :
    f ∈ Pk K x y ↔ f ∈ K.G.edgeSet ∧ ¬ (K.G.deleteEdges {f}).Reachable x y := by
  rw [Pk, Finset.mem_filter, mem_edgeFinset]

lemma Pk_subset (x y : Fin m) : Pk K x y ⊆ K.G.edgeFinset := Finset.filter_subset _ _

lemma Pk_comm (x y : Fin m) : Pk K x y = Pk K y x := by
  ext f; simp only [mem_Pk, reachable_comm]

lemma not_mem_Pk_self (x : Fin m) (f : Sym2 (Fin m)) : f ∉ Pk K x x := by
  rw [mem_Pk]; exact fun h => h.2 (Reachable.refl _)

lemma mem_Pk_trans {x y z : Fin m} {f : Sym2 (Fin m)} (h : f ∈ Pk K x z) :
    f ∈ Pk K x y ∨ f ∈ Pk K y z := by
  rw [mem_Pk] at h ⊢
  rw [mem_Pk]
  by_contra hc
  push Not at hc
  exact h.2 ((hc.1 h.1).trans (hc.2 h.1))

/-- The tree distance is the sum of the weights over the path edges. -/
lemma dist_eq_Pk (x y : Fin m) : K.dist x y = ∑ f ∈ Pk K x y, K.w f := by
  rw [WT.dist_eq_sum, Pk, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  by_cases h : f ∈ (K.path x y).edges
  · rw [if_pos h, if_pos ((WT.mem_path_edges K x y f).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((WT.mem_path_edges K x y f).mpr h'))]

/-- Side characterisation: `f` separates `a` from `b` iff exactly one of them is cut off from `r`. -/
lemma mem_Pk_iff_side (r : Fin m) {f : Sym2 (Fin m)} (hf : f ∈ K.G.edgeSet) (a b : Fin m) :
    f ∈ Pk K a b ↔
      ¬ ((¬ (K.G.deleteEdges {f}).Reachable r a) ↔ (¬ (K.G.deleteEdges {f}).Reachable r b)) := by
  rw [WT.sep_iff K r a b hf, WT.mem_path_edges, mem_Pk]
  exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩

end KSide

section Pe
variable {n m : ℕ} (K : WeightedTree (Fin m)) (q : Fin n → Fin m)

/-- The core path `P_e` of an edge `e = s(u, v)`: the path of `K` from `q u` to `q v`. -/
noncomputable def Pe (e : Sym2 (Fin n)) : Finset (Sym2 (Fin m)) :=
  Sym2.lift ⟨fun u v => Pk K (q u) (q v), fun _ _ => Pk_comm K _ _⟩ e

@[simp] lemma Pe_mk (u v : Fin n) : Pe K q s(u, v) = Pk K (q u) (q v) := rfl

lemma Pe_subset (e : Sym2 (Fin n)) : Pe K q e ⊆ K.G.edgeFinset := by
  induction e with
  | _ u v => exact Pk_subset K _ _

/-- The core path of `s(u, v)` has `K`-weight at most `w(u, v)` (non-expansiveness of `q`). -/
lemma sum_Pe_le_edgeCost (d : Fin n → Fin n → ℝ) (hq : ∀ u v, K.dist (q u) (q v) ≤ d u v)
    (e : Sym2 (Fin n)) : ∑ f ∈ Pe K q e, K.w f ≤ DoublingMST.edgeCost d e := by
  induction e with
  | _ u v =>
    rw [Pe_mk, ← dist_eq_Pk]
    show K.dist (q u) (q v) ≤ min (d u v) (d v u)
    refine le_min (hq u v) ?_
    rw [WT.dist_comm]; exact hq v u

/-- Double counting: summing over core paths counts each core edge with its multiplicity. -/
lemma sum_sum_Pe (A : Finset (Sym2 (Fin n))) (g : Sym2 (Fin m) → ℝ) :
    ∑ e ∈ A, ∑ f ∈ Pe K q e, g f =
      ∑ f ∈ K.G.edgeFinset, ((A.filter (fun e => f ∈ Pe K q e)).card : ℝ) * g f := by
  have h1 : ∀ e, ∑ f ∈ Pe K q e, g f = ∑ f ∈ K.G.edgeFinset, if f ∈ Pe K q e then g f else 0 := by
    intro e
    rw [← Finset.sum_filter]
    congr 1
    ext f
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨Pe_subset K q e h, h⟩, fun h => h.2⟩
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- Along a walk from `u` to `v`, every edge of the core path `q u → q v` lies on the core path of
some edge of the walk. -/
lemma exists_mem_Pe_of_walk {G : SimpleGraph (Fin n)} {u v : Fin n} (p : G.Walk u v)
    {f : Sym2 (Fin m)} (hf : f ∈ Pk K (q u) (q v)) : ∃ e ∈ p.edges, f ∈ Pe K q e := by
  induction p with
  | nil => exact absurd hf (not_mem_Pk_self K _ f)
  | @cons x y z h p ih =>
    rcases mem_Pk_trans K (y := q y) hf with h1 | h1
    · exact ⟨s(x, y), by simp, by simpa using h1⟩
    · obtain ⟨e, he, hfe⟩ := ih h1
      exact ⟨e, by simp [he], hfe⟩

/-- Parity: along a walk from `u` to `v`, the core edge `f` lies on an odd number of the core paths
of the walk's edges iff it lies on the core path `q u → q v`. -/
lemma odd_countP_iff {G : SimpleGraph (Fin n)} {u v : Fin n} (p : G.Walk u v)
    {f : Sym2 (Fin m)} (hf : f ∈ K.G.edgeSet) :
    Odd (p.edges.countP (fun e => decide (f ∈ Pe K q e))) ↔ f ∈ Pk K (q u) (q v) := by
  induction p with
  | nil =>
    simp only [Walk.edges_nil, List.countP_nil]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (not_mem_Pk_self K _ f)⟩
  | @cons x y z h p ih =>
    rw [Walk.edges_cons, List.countP_cons]
    have hxz := mem_Pk_iff_side K (q x) hf (q x) (q z)
    have hxy := mem_Pk_iff_side K (q x) hf (q x) (q y)
    have hyz := mem_Pk_iff_side K (q x) hf (q y) (q z)
    have hr : (K.G.deleteEdges {f}).Reachable (q x) (q x) := Reachable.refl _
    generalize List.countP (fun e => decide (f ∈ Pe K q e)) p.edges = c at ih ⊢
    split_ifs with hb
    · have hb' : f ∈ Pk K (q x) (q y) := decide_eq_true_iff.mp hb
      rw [Nat.odd_add_one, ih]
      generalize (f ∈ Pk K (q x) (q y)) = X at hb' hxy
      generalize (f ∈ Pk K (q x) (q z)) = Y at hxz ⊢
      generalize (f ∈ Pk K (q y) (q z)) = Z at hyz ⊢
      generalize (K.G.deleteEdges {f}).Reachable (q x) (q y) = B at hxy hyz
      generalize (K.G.deleteEdges {f}).Reachable (q x) (q z) = C at hxz hyz
      generalize (K.G.deleteEdges {f}).Reachable (q x) (q x) = A at hxz hxy hr
      tauto
    · have hb' : f ∉ Pk K (q x) (q y) := fun h' => hb (decide_eq_true_iff.mpr h')
      rw [add_zero, ih]
      generalize (f ∈ Pk K (q x) (q y)) = X at hb' hxy
      generalize (f ∈ Pk K (q x) (q z)) = Y at hxz ⊢
      generalize (f ∈ Pk K (q y) (q z)) = Z at hyz ⊢
      generalize (K.G.deleteEdges {f}).Reachable (q x) (q y) = B at hxy hyz
      generalize (K.G.deleteEdges {f}).Reachable (q x) (q z) = C at hxz hyz
      generalize (K.G.deleteEdges {f}).Reachable (q x) (q x) = A at hxz hxy hr
      tauto

/-- For a walk without repeated edges, the count is the number of distinct edges. -/
lemma card_filter_toFinset {α : Type*} [DecidableEq α] (l : List α) (hl : l.Nodup) (P : α → Prop)
    [DecidablePred P] : (l.toFinset.filter P).card = l.countP (fun a => decide (P a)) := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.filter _), List.toFinset_filter]
  simp

end Pe

end MTSPAL

end ASM1

section ASM2
-- from Solutions.AL.Hull

/-!
# The core paths of the hull edges: covering, domination, equality

`E` is a spanning tree on `Fin n`, `S` the terminals, `K` the core tree and `q` the map.
-/

open scoped Classical

namespace MTSPAL
open SimpleGraph TreeCoverLB MetricTSPSublinear

variable {n m : ℕ} {E : Finset (Sym2 (Fin n))} (hE : (DoublingMST.completeGraph n).IsSpanningTree E)
  (S : Finset (Fin n)) (K : WeightedTree (Fin m)) (q : Fin n → Fin m)

/-- A vertex of the core subtree `T⟨S⟩`: a terminal or an endpoint of a hull edge. -/
def IsHullVertex (E : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) (u : Fin n) : Prop :=
  u ∈ S ∨ ∃ e ∈ hull E S, u ∈ e

include hE

/-- The core paths `P_e` of the hull edges cover the core (its leaves are images of terminals). -/
lemma exists_hull_cover
    (hleaf : ∀ c, (∀ y₁ y₂, K.G.Adj c y₁ → K.G.Adj c y₂ → y₁ = y₂) → ∃ s ∈ S, q s = c)
    {f : Sym2 (Fin m)} (hf : f ∈ K.G.edgeSet) : ∃ e ∈ hull E S, f ∈ Pe K q e := by
  induction f with
  | _ a b =>
  obtain ⟨c1, hl1, _⟩ := WT.exists_leaf_side K a hf
  obtain ⟨s1, hs1, rfl⟩ := hleaf c1 hl1
  obtain ⟨c2, hl2, hc2⟩ := WT.exists_leaf_side K (q s1) hf
  obtain ⟨s2, hs2, rfl⟩ := hleaf c2 hl2
  have hmem : s(a, b) ∈ Pk K (q s1) (q s2) := (mem_Pk K).mpr ⟨hf, hc2⟩
  obtain ⟨p⟩ := reachable_of_spanConnected hE.1 s1 s2
  obtain ⟨e, he, hfe⟩ := exists_mem_Pe_of_walk K q p.bypass hmem
  refine ⟨e, ?_, hfe⟩
  have h1 := (mem_pathEdges_iff hE p.bypass p.bypass_isPath e).mpr he
  rw [hull, Finset.mem_filter]
  exact ⟨(Finset.mem_filter.mp h1).1, s1, hs1, s2, hs2, h1⟩

/-- Domination: if every core path `P_e` (`e ∈ E`) has `wC`-weight at most `wT e`, then the
`wC`-distance of `q u, q v` is at most the `wT`-tree distance of `u, v`. -/
lemma sum_Pk_le_treeDist (wC : Sym2 (Fin m) → ℝ) (hwC : ∀ f, 0 ≤ wC f) (wT : Sym2 (Fin n) → ℝ)
    (hb : ∀ e ∈ E, ∑ f ∈ Pe K q e, wC f ≤ wT e) (u v : Fin n) :
    ∑ f ∈ Pk K (q u) (q v), wC f ≤ treeDist E wT u v := by
  obtain ⟨p⟩ := reachable_of_spanConnected hE.1 u v
  rw [treeDist, pathEdges_eq_toFinset hE p.bypass p.bypass_isPath]
  have hE' : ∀ e ∈ p.bypass.edges.toFinset, e ∈ E := fun e he =>
    mem_of_mem_edgeSet (p.bypass.edges_subset_edgeSet (List.mem_toFinset.mp he))
  calc ∑ f ∈ Pk K (q u) (q v), wC f
      ≤ ∑ e ∈ p.bypass.edges.toFinset, ∑ f ∈ Pe K q e, wC f := by
        rw [sum_sum_Pe, Pk, Finset.sum_filter]
        apply Finset.sum_le_sum
        intro f hf
        split_ifs with hs
        · exact mul_nonneg (Nat.cast_nonneg _) (hwC f)
        · have hfP : f ∈ Pk K (q u) (q v) := (mem_Pk K).mpr ⟨mem_edgeFinset.mp hf, hs⟩
          obtain ⟨e, he, hfe⟩ := exists_mem_Pe_of_walk K q p.bypass hfP
          have hpos : 1 ≤ ((p.bypass.edges.toFinset.filter (fun e => f ∈ Pe K q e)).card : ℝ) := by
            have : 0 < (p.bypass.edges.toFinset.filter (fun e => f ∈ Pe K q e)).card :=
              Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr he, hfe⟩⟩
            exact_mod_cast this
          calc wC f = 1 * wC f := (one_mul _).symm
            _ ≤ _ := mul_le_mul_of_nonneg_right hpos (hwC f)
    _ ≤ ∑ e ∈ p.bypass.edges.toFinset, wT e := Finset.sum_le_sum (fun e he => hb e (hE' e he))

/-- Between two vertices of `T⟨S⟩` the tree path stays in the hull. -/
lemma pathEdges_subset_hull {u v : Fin n} (hu : IsHullVertex E S u) (hv : IsHullVertex E S v) :
    pathEdges E u v ⊆ hull E S := by
  intro g hg
  by_contra hgH
  have hgE : g ∈ E := (Finset.mem_filter.mp hg).1
  have hnotsep : ∀ s ∈ S, ∀ t ∈ S,
      (SimpleGraph.fromEdgeSet ((E : Set (Sym2 (Fin n))) \ {g})).Reachable s t := by
    intro s hs t ht
    by_contra h
    exact hgH (Finset.mem_filter.mpr ⟨hgE, s, hs, t, ht, Finset.mem_filter.mpr ⟨hgE, h⟩⟩)
  have side : ∀ x, IsHullVertex E S x →
      ∃ s ∈ S, (SimpleGraph.fromEdgeSet ((E : Set (Sym2 (Fin n))) \ {g})).Reachable x s := by
    rintro x (hx | ⟨h, hh, hxh⟩)
    · exact ⟨x, hx, Reachable.refl _⟩
    · obtain ⟨_, s1, hs1, s2, hs2, hsep⟩ := Finset.mem_filter.mp hh
      obtain ⟨p⟩ := reachable_of_spanConnected hE.1 s1 s2
      have hhp : h ∈ p.bypass.edges := (mem_pathEdges_iff hE _ p.bypass_isPath h).mp hsep
      have hgp : g ∉ p.bypass.edges := fun hgp => hgH (Finset.mem_filter.mpr
        ⟨hgE, s1, hs1, s2, hs2, (mem_pathEdges_iff hE _ p.bypass_isPath g).mpr hgp⟩)
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxh
      have hxs : x ∈ p.bypass.support := p.bypass.fst_mem_support_of_mem_edges hhp
      have hgw : g ∉ (p.bypass.takeUntil x hxs).edges := fun hh' =>
        hgp (p.bypass.edges_takeUntil_subset_edges hxs hh')
      have hr : ((grE E).deleteEdges {g}).Reachable s1 x := ⟨(p.bypass.takeUntil x hxs).toDeleteEdge g hgw⟩
      rw [grE_deleteEdges] at hr
      exact ⟨s1, hs1, hr.symm⟩
  obtain ⟨s, hs, hus⟩ := side u hu
  obtain ⟨t, ht, hvt⟩ := side v hv
  exact (Finset.mem_filter.mp hg).2 (hus.trans ((hnotsep s hs t ht).trans hvt.symm))

/-- Equality: if the `u`–`v` tree path lies in the hull, `wT = wC(P_e)` on hull edges, and every core
edge of positive `wC`-weight lies on exactly one hull path, then the `wT`-tree distance of `u, v` is
at most the `wC`-distance of `q u, q v`. -/
lemma treeDist_le_sum_Pk (wC : Sym2 (Fin m) → ℝ) (hwC : ∀ f, 0 ≤ wC f) (wT : Sym2 (Fin n) → ℝ)
    (hwT : ∀ e ∈ hull E S, wT e = ∑ f ∈ Pe K q e, wC f)
    (hone : ∀ f, wC f ≠ 0 → ((hull E S).filter (fun e => f ∈ Pe K q e)).card = 1)
    {u v : Fin n} (hsub : pathEdges E u v ⊆ hull E S) :
    treeDist E wT u v ≤ ∑ f ∈ Pk K (q u) (q v), wC f := by
  obtain ⟨p⟩ := reachable_of_spanConnected hE.1 u v
  rw [treeDist, Finset.sum_congr rfl (fun e he => hwT e (hsub he)), sum_sum_Pe, Pk, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro f hf
  by_cases h0 : wC f = 0
  · rw [h0, mul_zero]; split_ifs <;> simp
  · have h1 := hone f h0
    have hle : ((pathEdges E u v).filter (fun e => f ∈ Pe K q e)).card ≤ 1 :=
      h1 ▸ Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hc | hc
    · rw [hc, Nat.cast_zero, zero_mul]; split_ifs
      · exact le_rfl
      · exact hwC f
    · have hodd : Odd (p.bypass.edges.countP (fun e => decide (f ∈ Pe K q e))) := by
        rw [← card_filter_toFinset _ p.bypass_isPath.isTrail.edges_nodup,
          ← pathEdges_eq_toFinset hE p.bypass p.bypass_isPath, hc]
        exact odd_one
      have hfP := ((odd_countP_iff K q p.bypass (mem_edgeFinset.mp hf)).mp hodd)
      rw [hc, Nat.cast_one, one_mul, if_pos ((mem_Pk K).mp hfP).2]

end MTSPAL

end ASM2

section ASM3
-- from Solutions.AL.Reduce

/-!
# Lowering weights along paths (the second step of the core alignment)

`red W P t` scales the weights `W` on the set `P` down by a common factor so that their sum
becomes `t`, if it exceeds `t`; otherwise it changes nothing. `redList` does this for a list of
pairs `(P, t)` in turn.
-/

open scoped Classical

namespace MTSPAL

variable {α : Type*} [Fintype α]

/-- Scale `W` down on `P` so that `∑_{P} W ≤ t`. -/
noncomputable def red (W : α → ℝ) (P : Finset α) (t : ℝ) : α → ℝ :=
  if ∑ f ∈ P, W f ≤ t then W else fun f => if f ∈ P then W f * (t / ∑ g ∈ P, W g) else W f

/-- Apply `red` for each pair of the list in turn. -/
noncomputable def redList : List (Finset α × ℝ) → (α → ℝ) → (α → ℝ)
  | [], W => W
  | pt :: L, W => redList L (red W pt.1 pt.2)

omit [Fintype α] in
lemma red_apply (W : α → ℝ) (P : Finset α) (t : ℝ) (f : α) :
    red W P t f = if ∑ g ∈ P, W g ≤ t then W f else if f ∈ P then W f * (t / ∑ g ∈ P, W g) else W f := by
  unfold red; by_cases h : ∑ g ∈ P, W g ≤ t <;> simp [h]

omit [Fintype α] in
lemma red_nonneg (W : α → ℝ) (P : Finset α) (t : ℝ) (hW : ∀ f, 0 ≤ W f) (ht : 0 ≤ t) (f : α) :
    0 ≤ red W P t f := by
  rw [red_apply]
  split_ifs with h h'
  · exact hW f
  · have hs : 0 ≤ ∑ g ∈ P, W g := Finset.sum_nonneg (fun g _ => hW g)
    exact mul_nonneg (hW f) (div_nonneg ht hs)
  · exact hW f

omit [Fintype α] in
lemma red_le (W : α → ℝ) (P : Finset α) (t : ℝ) (hW : ∀ f, 0 ≤ W f) (ht : 0 ≤ t) (f : α) :
    red W P t f ≤ W f := by
  rw [red_apply]
  split_ifs with h h'
  · exact le_rfl
  · have h := not_le.mp h
    have hs : 0 < ∑ g ∈ P, W g := lt_of_le_of_lt ht h
    have h1 : t / ∑ g ∈ P, W g ≤ 1 := (div_le_one hs).mpr h.le
    calc W f * (t / ∑ g ∈ P, W g) ≤ W f * 1 := mul_le_mul_of_nonneg_left h1 (hW f)
      _ = W f := mul_one _
  · exact le_rfl

omit [Fintype α] in
lemma red_sum_le (W : α → ℝ) (P : Finset α) (t : ℝ) (ht : 0 ≤ t) :
    ∑ f ∈ P, red W P t f ≤ t := by
  by_cases h : ∑ g ∈ P, W g ≤ t
  · simp only [red_apply, if_pos h]; exact h
  · have h' := not_le.mp h
    have hs : 0 < ∑ g ∈ P, W g := lt_of_le_of_lt ht h'
    simp only [red_apply, if_neg h]
    rw [Finset.sum_congr rfl (fun f hf => if_pos hf), ← Finset.sum_mul]
    rw [mul_div_cancel₀ _ hs.ne']

lemma red_loss (W : α → ℝ) (P : Finset α) (t : ℝ) (ht : 0 ≤ t) :
    ∑ f, (W f - red W P t f) ≤ max 0 (∑ f ∈ P, W f - t) := by
  by_cases h : ∑ g ∈ P, W g ≤ t
  · simp [red_apply, if_pos h]
  · have h' := not_le.mp h
    have hs : 0 < ∑ g ∈ P, W g := lt_of_le_of_lt ht h'
    simp only [red_apply, if_neg h]
    have : ∀ f, W f - (if f ∈ P then W f * (t / ∑ g ∈ P, W g) else W f) =
        if f ∈ P then W f - W f * (t / ∑ g ∈ P, W g) else 0 := by
      intro f; split_ifs <;> ring
    simp only [this]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_sub_distrib,
      ← Finset.sum_mul, mul_div_cancel₀ _ hs.ne']
    exact le_max_right _ _

lemma redList_spec (L : List (Finset α × ℝ)) (hL : ∀ pt ∈ L, 0 ≤ pt.2) :
    ∀ W : α → ℝ, (∀ f, 0 ≤ W f) →
      (∀ f, 0 ≤ redList L W f) ∧ (∀ f, redList L W f ≤ W f) ∧
      (∀ pt ∈ L, ∑ f ∈ pt.1, redList L W f ≤ pt.2) ∧
      ∑ f, (W f - redList L W f) ≤ (L.map (fun pt => max 0 (∑ f ∈ pt.1, W f - pt.2))).sum := by
  induction L with
  | nil =>
    intro W hW
    simp [redList, hW]
  | cons pt L ih =>
    intro W hW
    have ht : 0 ≤ pt.2 := hL pt (by simp)
    have hW' := red_nonneg W pt.1 pt.2 hW ht
    obtain ⟨h1, h2, h3, h4⟩ := ih (fun p hp => hL p (by simp [hp])) _ hW'
    simp only [redList]
    refine ⟨h1, fun f => (h2 f).trans (red_le W pt.1 pt.2 hW ht f), ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact (Finset.sum_le_sum (fun f _ => h2 f)).trans (red_sum_le W p.1 p.2 ht)
      · exact h3 p hp
    · have hsplit : ∑ f, (W f - redList L (red W pt.1 pt.2) f) =
          ∑ f, (W f - red W pt.1 pt.2 f) + ∑ f, (red W pt.1 pt.2 f - redList L (red W pt.1 pt.2) f) := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun f _ => by ring)
      rw [hsplit, List.map_cons, List.sum_cons]
      refine add_le_add (red_loss W pt.1 pt.2 ht) (h4.trans ?_)
      apply List.sum_le_sum
      intro p _
      apply max_le_max le_rfl
      exact sub_le_sub_right (Finset.sum_le_sum (fun f _ => red_le W pt.1 pt.2 hW ht f)) _

end MTSPAL

end ASM3

section ASM4
-- from Solutions.AL.CoreAlignment

/-!
# Lemma 5.5 (Core Alignment), discrete version

Azarmehr–Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283,
Lemma 5.5 and its proof (§5.4, pp.19–21).

Discrete model: the core is a weighted tree `K` on `Fin m` (the continuous `R(C)` is replaced by a
subdivision), `q : Fin n → Fin m` is non-expansive, the leaves of `K` are images of terminals, and
`w(K) ≥ K(S) − η`. The tree `T1` is a dominated shortening `w1` of the MST `E` with
`w(T) − w(T1) ≤ β`.

The aligned core `C*` is `K` with new weights `wC ≤ wK` (the set `B` of the paper is recorded by the
weight removed, `w(B) = w(K) − w(C*)`), and the comparison tree `T*` is a shortening `wT` of `w1`.

Construction (as in the paper): `B0` = core edges covered by at least two (or no) hull paths `P_e` are
set to `0`; then for every `e ∈ E` in turn the weights along `P_e` are scaled down until
`wC(P_e) ≤ w1(e)`; finally `wT e = d_{C*}(q u, q v)` on hull edges `e = s(u, v)` and `wT = w1` elsewhere.
Constants: `w(B) ≤ 2D + η + β` and `w(T1) − w(T*) ≤ 4D + 2η + β` (paper, with `η = 0`,
`β = 4D + εM̂`: `6D + εM̂` and `8D + εM̂`).
-/

open scoped Classical

namespace MTSPAL
open SimpleGraph TreeCoverLB MetricTSPSublinear

/-- The tree `K` with its edge weights replaced by `w'`. -/
def reweight {X : Type*} (K : WeightedTree X) (w' : Sym2 X → ℝ) (h : ∀ e ∈ K.G.edgeSet, 0 ≤ w' e) :
    WeightedTree X :=
  { G := K.G, isTree := K.isTree, w := w', w_nonneg := h }

/-- **Lemma 5.5 (Core Alignment)**, discrete version. -/
theorem core_alignment {n m : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (E : Finset (Sym2 (Fin n))) (hE : DoublingMST.IsMSTOf d Finset.univ E)
    (S : Finset (Fin n)) (K : WeightedTree (Fin m)) (q : Fin n → Fin m)
    (hq : ∀ u v, K.dist (q u) (q v) ≤ d u v)
    (hleaf : ∀ c, (∀ y₁ y₂, K.G.Adj c y₁ → K.G.Adj c y₂ → y₁ = y₂) → ∃ s ∈ S, q s = c)
    (η : ℝ) (hK : cutLP d S - η ≤ ∑ f ∈ K.G.edgeFinset, K.w f)
    (w1 : Sym2 (Fin n) → ℝ) (hw1 : IsDominatedShortening d E w1)
    (β : ℝ) (hT1 : ∑ e ∈ E, (DoublingMST.edgeCost d e - w1 e) ≤ β) :
    ∃ (C : WeightedTree (Fin m)) (wT : Sym2 (Fin n) → ℝ),
      -- the aligned core `C*`: `K` with smaller weights
      C.G = K.G ∧ (∀ f ∈ K.G.edgeSet, C.w f ≤ K.w f) ∧
      -- the comparison tree `T*`: a shortening of `T1`
      (∀ e ∈ E, 0 ≤ wT e ∧ wT e ≤ w1 e) ∧
      -- property 3: edges outside `T⟨S⟩` keep their `T1`-weight
      (∀ e ∈ E, e ∉ hull E S → wT e = w1 e) ∧
      -- definition of `T*` on hull edges
      (∀ u v, s(u, v) ∈ hull E S → wT s(u, v) = C.dist (q u) (q v)) ∧
      -- property 1: `w(T*⟨S⟩) = w(C*)`
      ∑ e ∈ hull E S, wT e = ∑ f ∈ K.G.edgeFinset, C.w f ∧
      -- property 2: domination, with equality on `T⟨S⟩`
      (∀ u v, C.dist (q u) (q v) ≤ treeDist E wT u v) ∧
      (∀ u v, IsHullVertex E S u → IsHullVertex E S v → C.dist (q u) (q v) = treeDist E wT u v) ∧
      -- `w(B) ≤ 2D + η + β`
      ∑ f ∈ K.G.edgeFinset, K.w f - ∑ f ∈ K.G.edgeFinset, C.w f ≤
        2 * (DoublingMST.mstWeight d - cutLP d Finset.univ) + η + β ∧
      -- `w(T1) − w(T*) ≤ 4D + 2η + β`
      ∑ e ∈ E, (w1 e - wT e) ≤ 4 * (DoublingMST.mstWeight d - cutLP d Finset.univ) + 2 * η + β ∧
      IsDominatedShortening d E wT := by
  have hEt := hE.1
  have hHE : hull E S ⊆ E := Finset.filter_subset _ _
  -- cover counts and the first step (`B0`)
  let cnt : Sym2 (Fin m) → ℕ := fun f => ((hull E S).filter (fun e => f ∈ Pe K q e)).card
  let w0 : Sym2 (Fin m) → ℝ := fun f => if cnt f = 1 then K.w f else 0
  have hcnt_mem : ∀ f, cnt f ≠ 0 → f ∈ K.G.edgeSet := by
    intro f hf
    obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hf)
    exact mem_edgeFinset.mp (Pe_subset K q e (Finset.mem_filter.mp he).2)
  have hw0 : ∀ f, 0 ≤ w0 f := by
    intro f
    simp only [w0]
    split_ifs with h
    · exact K.w_nonneg f (hcnt_mem f (by omega))
    · exact le_rfl
  have hw0K : ∀ f ∈ K.G.edgeSet, w0 f ≤ K.w f := by
    intro f hf
    simp only [w0]
    split_ifs
    · exact le_rfl
    · exact K.w_nonneg f hf
  -- the second step: lower the weights along every `P_e`, `e ∈ E`
  let L : List (Finset (Sym2 (Fin m)) × ℝ) := E.toList.map (fun e => (Pe K q e, w1 e))
  have hL : ∀ pt ∈ L, 0 ≤ pt.2 := by
    intro pt hpt
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpt
    exact (hw1.1 e (Finset.mem_toList.mp he)).1
  obtain ⟨hC0, hCle, hCP, hCloss⟩ := redList_spec L hL w0 hw0
  set wC := redList L w0 with hwCdef
  have hPe : ∀ e ∈ E, ∑ f ∈ Pe K q e, wC f ≤ w1 e := fun e he =>
    hCP (Pe K q e, w1 e) (List.mem_map.mpr ⟨e, Finset.mem_toList.mpr he, rfl⟩)
  have hlist : (L.map (fun pt => max 0 (∑ f ∈ pt.1, w0 f - pt.2))).sum ≤ β := by
    rw [List.map_map, Finset.sum_map_toList]
    refine le_trans (Finset.sum_le_sum (fun e he => ?_)) hT1
    have h1 : ∑ f ∈ Pe K q e, w0 f ≤ DoublingMST.edgeCost d e :=
      (Finset.sum_le_sum (fun f hf => hw0K f (mem_edgeFinset.mp (Pe_subset K q e hf)))).trans
        (sum_Pe_le_edgeCost K q d hq e)
    have h2 := hw1.1 e he
    show max 0 (∑ f ∈ Pe K q e, w0 f - w1 e) ≤ DoublingMST.edgeCost d e - w1 e
    exact max_le (by linarith [h2.2]) (by linarith)
  have hone : ∀ f, wC f ≠ 0 → cnt f = 1 := by
    intro f hf
    by_contra h
    have h1 := hCle f
    have h2 := hC0 f
    have h3 : w0 f = 0 := if_neg h
    exact hf (le_antisymm (h3 ▸ h1) h2)
  -- the aligned core and the comparison tree
  let C : WeightedTree (Fin m) := reweight K wC (fun f _ => hC0 f)
  let wT : Sym2 (Fin n) → ℝ := fun e => if e ∈ hull E S then ∑ f ∈ Pe K q e, wC f else w1 e
  have hwT_le : ∀ e ∈ E, ∑ f ∈ Pe K q e, wC f ≤ wT e := by
    intro e he
    simp only [wT]
    split_ifs
    · exact le_rfl
    · exact hPe e he
  have hwTE : ∀ e ∈ E, 0 ≤ wT e ∧ wT e ≤ w1 e := by
    intro e he
    simp only [wT]
    split_ifs
    · exact ⟨Finset.sum_nonneg (fun f _ => hC0 f), hPe e he⟩
    · exact ⟨(hw1.1 e he).1, le_rfl⟩
  have hCdist : ∀ x y, C.dist x y = ∑ f ∈ Pk K x y, wC f := fun x y => dist_eq_Pk C x y
  have hwTH : ∀ e ∈ hull E S, wT e = ∑ f ∈ Pe K q e, wC f := fun e he => if_pos he
  -- property 1
  have hsumH : ∑ e ∈ hull E S, wT e = ∑ f ∈ K.G.edgeFinset, wC f := by
    rw [Finset.sum_congr rfl hwTH, sum_sum_Pe]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    by_cases h : cnt f = 1
    · have h' : (((hull E S).filter (fun e => f ∈ Pe K q e)).card : ℝ) = 1 := by exact_mod_cast h
      rw [h', one_mul]
    · have : wC f = 0 := by_contra (fun h' => h (hone f h'))
      rw [this, mul_zero]
  -- the weight of `B`
  have h44 := lemma_4_4 d hd E hE S
  have hKH : ∑ e ∈ hull E S, ∑ f ∈ Pe K q e, K.w f ≤ DoublingMST.treeWeight d (hull E S) :=
    Finset.sum_le_sum (fun e _ => sum_Pe_le_edgeCost K q d hq e)
  have hcover := fun {f : Sym2 (Fin m)} (hf : f ∈ K.G.edgeSet) => exists_hull_cover hEt S K q hleaf hf
  have hloss1 : ∑ f ∈ K.G.edgeFinset, (K.w f - w0 f) ≤
      ∑ e ∈ hull E S, ∑ f ∈ Pe K q e, K.w f - ∑ f ∈ K.G.edgeFinset, K.w f := by
    rw [sum_sum_Pe, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro f hf
    have hc1 : 1 ≤ cnt f := by
      obtain ⟨e, he, hfe⟩ := hcover (mem_edgeFinset.mp hf)
      exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hfe⟩⟩
    have hKf := K.w_nonneg f (mem_edgeFinset.mp hf)
    show K.w f - (if cnt f = 1 then K.w f else 0) ≤ (cnt f : ℝ) * K.w f - K.w f
    split_ifs with h
    · rw [h, Nat.cast_one]; linarith
    · have h2 : (2 : ℝ) ≤ cnt f := by exact_mod_cast (by omega : 2 ≤ cnt f)
      nlinarith
  have hloss2 : ∑ f ∈ K.G.edgeFinset, (w0 f - wC f) ≤ β :=
    (Finset.sum_le_univ_sum_of_nonneg (fun f => sub_nonneg.mpr (hCle f))).trans (hCloss.trans hlist)
  have hB : ∑ f ∈ K.G.edgeFinset, K.w f - ∑ f ∈ K.G.edgeFinset, wC f ≤
      2 * (DoublingMST.mstWeight d - cutLP d Finset.univ) + η + β := by
    have hsplit : ∑ f ∈ K.G.edgeFinset, K.w f - ∑ f ∈ K.G.edgeFinset, wC f =
        ∑ f ∈ K.G.edgeFinset, (K.w f - w0 f) + ∑ f ∈ K.G.edgeFinset, (w0 f - wC f) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun f _ => by ring)
    linarith [h44.1]
  refine ⟨C, wT, rfl, fun f hf => (hCle f).trans (hw0K f hf), hwTE, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- property 3
    intro e _ he
    exact if_neg he
  · -- `wT` on hull edges is the aligned-core distance
    intro u v he
    rw [hwTH _ he, hCdist, Pe_mk]
  · exact hsumH
  · -- domination
    intro u v
    rw [hCdist]
    exact sum_Pk_le_treeDist hEt K q wC hC0 wT hwT_le u v
  · -- equality on `T⟨S⟩`
    intro u v hu hv
    rw [hCdist]
    exact le_antisymm (sum_Pk_le_treeDist hEt K q wC hC0 wT hwT_le u v)
      (treeDist_le_sum_Pk hEt S K q wC hC0 wT hwTH hone (pathEdges_subset_hull hEt S hu hv))
  · exact hB
  · -- `w(T1) − w(T*)`
    have hsub : ∑ e ∈ hull E S, (w1 e - wT e) = ∑ e ∈ E, (w1 e - wT e) :=
      Finset.sum_subset hHE (fun e _ hn => by simp only [wT, if_neg hn, sub_self])
    rw [← hsub, Finset.sum_sub_distrib, hsumH]
    have hw1H : ∑ e ∈ hull E S, w1 e ≤ DoublingMST.treeWeight d (hull E S) :=
      Finset.sum_le_sum (fun e he => (hw1.1 e (hHE he)).2)
    linarith [h44.1]
  · -- `T*` is a dominated shortening
    refine ⟨fun e he => ⟨(hwTE e he).1, (hwTE e he).2.trans (hw1.1 e he).2⟩, fun u v => ?_⟩
    refine le_trans ?_ (hw1.2 u v)
    exact Finset.sum_le_sum (fun e he => (hwTE e (Finset.mem_filter.mp he).1).2)

end MTSPAL

end ASM4

open scoped Classical

open MetricTSPSublinear in
theorem solution {n m : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (E : Finset (Sym2 (Fin n))) (hE : DoublingMST.IsMSTOf d Finset.univ E)
    (S : Finset (Fin n)) (K : TreeCoverLB.WeightedTree (Fin m)) (q : Fin n → Fin m)
    (hq : ∀ u v, K.dist (q u) (q v) ≤ d u v)
    (hleaf : ∀ c, (∀ y₁ y₂, K.G.Adj c y₁ → K.G.Adj c y₂ → y₁ = y₂) → ∃ s ∈ S, q s = c)
    (η : ℝ) (hK : cutLP d S - η ≤ ∑ f ∈ K.G.edgeFinset, K.w f)
    (w1 : Sym2 (Fin n) → ℝ) (hw1 : IsDominatedShortening d E w1)
    (β : ℝ) (hT1 : ∑ e ∈ E, (DoublingMST.edgeCost d e - w1 e) ≤ β) :
    ∃ (C : TreeCoverLB.WeightedTree (Fin m)) (wT : Sym2 (Fin n) → ℝ),
      -- the aligned core `C*`: `K` with smaller weights
      C.G = K.G ∧ (∀ f ∈ K.G.edgeSet, C.w f ≤ K.w f) ∧
      -- the comparison tree `T*`: a shortening of `T1`
      (∀ e ∈ E, 0 ≤ wT e ∧ wT e ≤ w1 e) ∧
      -- property 3: edges outside `T⟨S⟩` keep their `T1`-weight
      (∀ e ∈ E, e ∉ hull E S → wT e = w1 e) ∧
      -- definition of `T*` on hull edges
      (∀ u v, s(u, v) ∈ hull E S → wT s(u, v) = C.dist (q u) (q v)) ∧
      -- property 1: `w(T*⟨S⟩) = w(C*)`
      ∑ e ∈ hull E S, wT e = ∑ f ∈ K.G.edgeFinset, C.w f ∧
      -- property 2: domination, with equality on `T⟨S⟩`
      (∀ u v, C.dist (q u) (q v) ≤ treeDist E wT u v) ∧
      (∀ u v, (u ∈ S ∨ ∃ e ∈ hull E S, u ∈ e) → (v ∈ S ∨ ∃ e ∈ hull E S, v ∈ e) → C.dist (q u) (q v) = treeDist E wT u v) ∧
      -- `w(B) ≤ 2D + η + β`
      ∑ f ∈ K.G.edgeFinset, K.w f - ∑ f ∈ K.G.edgeFinset, C.w f ≤
        2 * (DoublingMST.mstWeight d - cutLP d Finset.univ) + η + β ∧
      -- `w(T1) − w(T*) ≤ 4D + 2η + β`
      ∑ e ∈ E, (w1 e - wT e) ≤ 4 * (DoublingMST.mstWeight d - cutLP d Finset.univ) + 2 * η + β ∧
      IsDominatedShortening d E wT :=
  MTSPAL.core_alignment d hd E hE S K q hq hleaf η hK w1 hw1 β hT1
