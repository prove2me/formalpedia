-- Prove2me | solution 1 for MetricTSPSublinear.claim_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:54:49.485464+00:00
-- url     : https://prove2.me/submissions/8c217527-c60a-456d-bd59-98ebc4ed1ba5

import Definitions.Def_MetricTSPSublinear_IsDualFeasible
import Definitions.Def_MetricTSPSublinear_IsPort
import Definitions.Def_TreeCoverLB_WeightedTree
import Mathlib
import Theorems.Thm_MetricTSPSublinear_cutLP_weak_duality

/-!
# Generic lemmas on trees and weighted trees (for the gluing claim 6.1)
-/

open scoped Classical

namespace MTSPGL
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

end MTSPGL


/-!
# Cells of a tree core: projections onto cells

The (subdivided) core is a finite weighted tree `K` on `Fin m`; the cells are node sets `cellNodes P`,
each inducing a connected subgraph, and every edge of `K` lies inside exactly one cell.
The projection `proj P x` of a node `x` onto a nonempty cell `P` is the unique node `p ∈ P` reachable from `x`
by a walk using no edge inside `P`.
-/

open scoped Classical

namespace MTSPGL
open SimpleGraph TreeCoverLB

variable {m : ℕ} (K : WeightedTree (Fin m)) {ι : Type*} (cellNodes : ι → Finset (Fin m))

/-- The edge `e` lies inside the cell `P` (both endpoints are nodes of `P`). -/
def Inside (P : ι) (e : Sym2 (Fin m)) : Prop := ∀ z ∈ e, z ∈ cellNodes P

/-- A port of the cell `P`: a node of `P` shared with another cell. -/
def IsPort (P : ι) (p : Fin m) : Prop := p ∈ cellNodes P ∧ ∃ R, R ≠ P ∧ p ∈ cellNodes R

/-- `p` is the projection of `x` onto `P`: `p ∈ P`, reachable from `x` without using an edge inside `P`. -/
def IsProj (P : ι) (x p : Fin m) : Prop :=
  p ∈ cellNodes P ∧ ∃ W : K.G.Walk x p, ∀ e ∈ W.edges, ¬ Inside cellNodes P e

/-- The projection of `x` onto the cell `P` (junk `x` if `P` is empty). -/
noncomputable def proj (P : ι) (x : Fin m) : Fin m :=
  if h : ∃ p, IsProj K cellNodes P x p then h.choose else x

section Hyp
variable (hconn : ∀ P, (K.G.induce (cellNodes P : Set (Fin m))).Preconnected)
variable (hedge : ∀ a b, K.G.Adj a b → ∃! P, a ∈ cellNodes P ∧ b ∈ cellNodes P)

include hconn in
/-- Cells are convex: the tree path between two nodes of a cell stays inside it. -/
lemma path_inside {P : ι} {a b : Fin m} (ha : a ∈ cellNodes P) (hb : b ∈ cellNodes P) :
    ∀ e ∈ (K.path a b).edges, Inside cellNodes P e := by
  intro e he
  obtain ⟨W⟩ := hconn P ⟨a, ha⟩ ⟨b, hb⟩
  have he' := WT.path_edges_subset K (W.map (Embedding.induce _).toHom) he
  rw [Walk.edges_map, List.mem_map] at he'
  obtain ⟨e', -, rfl⟩ := he'
  intro z hz
  induction e' with
  | _ x y =>
    simp only [Sym2.map_mk, Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact x.2
    · exact y.2

include hedge in
lemma inside_unique {e : Sym2 (Fin m)} (he : e ∈ K.G.edgeSet) {P R : ι}
    (hP : Inside cellNodes P e) (hR : Inside cellNodes R e) : P = R := by
  induction e with
  | _ a b =>
    obtain ⟨Q, -, hQ⟩ := hedge a b he
    rw [hQ P ⟨hP a (Sym2.mem_mk_left a b), hP b (Sym2.mem_mk_right a b)⟩,
      hQ R ⟨hR a (Sym2.mem_mk_left a b), hR b (Sym2.mem_mk_right a b)⟩]

include hconn in
lemma isProj_unique {P : ι} {x p p' : Fin m} (h : IsProj K cellNodes P x p)
    (h' : IsProj K cellNodes P x p') : p = p' := by
  obtain ⟨hp, W, hW⟩ := h
  obtain ⟨hp', W', hW'⟩ := h'
  by_contra hne
  obtain ⟨z, -, hz⟩ := exists_first_edge (K.path p p') hne
  have hin := path_inside K cellNodes hconn hp hp' _ hz
  have := WT.path_edges_subset K (W.reverse.append W') hz
  rw [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse] at this
  rcases this with h1 | h1
  · exact hW _ h1 hin
  · exact hW' _ h1 hin

lemma exists_isProj_aux {P : ι} : ∀ {x r : Fin m} (_ : K.G.Walk x r), r ∈ cellNodes P →
    ∃ p, IsProj K cellNodes P x p := by
  intro x r W
  induction W with
  | nil => intro hr; exact ⟨_, hr, Walk.nil, by simp⟩
  | @cons x y r h W ih =>
    intro hr
    obtain ⟨p, hp, W', hW'⟩ := ih hr
    by_cases hx : x ∈ cellNodes P
    · exact ⟨x, hx, Walk.nil, by simp⟩
    · refine ⟨p, hp, Walk.cons h W', ?_⟩
      intro e he hin
      rw [Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact hx (hin x (Sym2.mem_mk_left _ _))
      · exact hW' e he hin

lemma proj_spec {P : ι} (hP : (cellNodes P).Nonempty) (x : Fin m) :
    IsProj K cellNodes P x (proj K cellNodes P x) := by
  have h : ∃ p, IsProj K cellNodes P x p := by
    obtain ⟨r, hr⟩ := hP
    obtain ⟨W⟩ := K.isTree.connected.preconnected x r
    exact exists_isProj_aux K cellNodes W hr
  unfold proj
  rw [dif_pos h]
  exact h.choose_spec

include hconn in
lemma proj_of_mem {P : ι} {x : Fin m} (hx : x ∈ cellNodes P) : proj K cellNodes P x = x :=
  isProj_unique K cellNodes hconn (proj_spec K cellNodes ⟨x, hx⟩ x) ⟨hx, Walk.nil, by simp⟩

omit hconn in
lemma proj_mem {P : ι} (hP : (cellNodes P).Nonempty) (x : Fin m) :
    proj K cellNodes P x ∈ cellNodes P :=
  (proj_spec K cellNodes hP x).1

include hconn hedge in
/-- Two nodes of a cell `P₀` have the same projection onto any other cell. -/
lemma proj_eq_of_mem {P₀ P : ι} (hne : P₀ ≠ P) (hP : (cellNodes P).Nonempty) {x y : Fin m}
    (hx : x ∈ cellNodes P₀) (hy : y ∈ cellNodes P₀) :
    proj K cellNodes P x = proj K cellNodes P y := by
  obtain ⟨hp, W, hW⟩ := proj_spec K cellNodes hP y
  refine isProj_unique K cellNodes hconn (proj_spec K cellNodes hP x) ⟨hp, (K.path x y).append W, ?_⟩
  intro e he hin
  rw [Walk.edges_append, List.mem_append] at he
  rcases he with he | he
  · exact hne (inside_unique K cellNodes hedge ((K.path x y).edges_subset_edgeSet he)
      (path_inside K cellNodes hconn hx hy e he) hin)
  · exact hW e he hin

include hconn hedge in
/-- The projection onto `P` of a node of another cell is a port of `P`. -/
lemma proj_isPort {P R : ι} (hRP : R ≠ P) (hP : (cellNodes P).Nonempty) {x : Fin m}
    (hx : x ∈ cellNodes R) : IsPort cellNodes P (proj K cellNodes P x) := by
  by_cases hxP : x ∈ cellNodes P
  · rw [proj_of_mem K cellNodes hconn hxP]
    exact ⟨hxP, R, hRP, hx⟩
  · obtain ⟨hp, W, hW⟩ := proj_spec K cellNodes hP x
    have hne : proj K cellNodes P x ≠ x := fun h => hxP (h ▸ hp)
    obtain ⟨z, hz, hzW⟩ := exists_first_edge W.reverse hne
    rw [Walk.edges_reverse, List.mem_reverse] at hzW
    have hzP : z ∉ cellNodes P := by
      intro hzP
      apply hW _ hzW
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hp
      · exact hzP
    obtain ⟨Q, hQ, -⟩ := hedge _ _ hz
    exact ⟨hp, Q, fun h => hzP (h ▸ hQ.2), hQ.1⟩

include hconn in
/-- An edge on the path between two projections onto `P` lies inside `P` and on the original path. -/
lemma path_proj {P : ι} (hP : (cellNodes P).Nonempty) (x y : Fin m) {e : Sym2 (Fin m)}
    (he : e ∈ (K.path (proj K cellNodes P x) (proj K cellNodes P y)).edges) :
    Inside cellNodes P e ∧ e ∈ (K.path x y).edges := by
  obtain ⟨hpx, Wx, hWx⟩ := proj_spec K cellNodes hP x
  obtain ⟨hpy, Wy, hWy⟩ := proj_spec K cellNodes hP y
  have hin := path_inside K cellNodes hconn hpx hpy e he
  refine ⟨hin, ?_⟩
  rw [WT.mem_path_edges] at he ⊢
  intro hxy
  apply he
  have h1 : (K.G.deleteEdges {e}).Reachable x (proj K cellNodes P x) :=
    ⟨Wx.toDeleteEdge e (fun h => hWx e h hin)⟩
  have h2 : (K.G.deleteEdges {e}).Reachable y (proj K cellNodes P y) :=
    ⟨Wy.toDeleteEdge e (fun h => hWy e h hin)⟩
  exact h1.symm.trans (hxy.trans h2)

include hconn hedge in
/-- The pieces of the `x`–`y` path in the cells add up to at most its length. -/
lemma sum_dist_proj_le [Fintype ι] (hne : ∀ P, (cellNodes P).Nonempty) (x y : Fin m) :
    ∑ P, K.dist (proj K cellNodes P x) (proj K cellNodes P y) ≤ K.dist x y := by
  simp only [WT.dist_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun e he => ?_)
  rw [mem_edgeFinset] at he
  by_cases h : ∃ P₀, e ∈ (K.path (proj K cellNodes P₀ x) (proj K cellNodes P₀ y)).edges
  · obtain ⟨P₀, hP₀⟩ := h
    obtain ⟨hin₀, hxy⟩ := path_proj K cellNodes hconn (hne P₀) x y hP₀
    rw [Finset.sum_eq_single P₀, if_pos hP₀, if_pos hxy]
    · intro P _ hP
      rw [if_neg]
      intro hP'
      exact hP (inside_unique K cellNodes hedge he
        (path_proj K cellNodes hconn (hne P) x y hP').1 hin₀)
    · intro h; exact absurd (Finset.mem_univ _) h
  · push Not at h
    simp only [h, if_false, Finset.sum_const_zero]
    split_ifs
    · exact K.w_nonneg e he
    · exact le_refl 0

include hconn hedge in
/-- Every port `p` of `P` is the projection of some leaf of `K` outside `P`, provided the other cell
containing `p` contains an edge. -/
lemma exists_leaf_proj {P : ι} {p : Fin m} (hport : IsPort cellNodes P p)
    (hcellEdge : ∀ R, ∃ a b, K.G.Adj a b ∧ a ∈ cellNodes R ∧ b ∈ cellNodes R) :
    ∃ c, (∀ y₁ y₂, K.G.Adj c y₁ → K.G.Adj c y₂ → y₁ = y₂) ∧ c ∉ cellNodes P ∧
      proj K cellNodes P c = p := by
  obtain ⟨hp, R, hRP, hpR⟩ := hport
  obtain ⟨a, b, hab, ha, hb⟩ := hcellEdge R
  -- a neighbour `z` of `p` inside `R`
  have hz : ∃ z, K.G.Adj p z ∧ z ∈ cellNodes R := by
    by_cases hpa : p = a
    · exact ⟨b, hpa ▸ hab, hb⟩
    · obtain ⟨z, hz, hzp⟩ := exists_first_edge (K.path p a) hpa
      exact ⟨z, hz, path_inside K cellNodes hconn hpR ha _ hzp z (Sym2.mem_mk_right _ _)⟩
  obtain ⟨z, hpz, hzR⟩ := hz
  have hzP : z ∉ cellNodes P := by
    intro hzP
    exact hRP (inside_unique K cellNodes hedge (e := s(p, z)) (K.G.mem_edgeSet.mpr hpz)
      (fun w hw => by rcases Sym2.mem_iff.mp hw with h | h <;> rw [h] <;> assumption)
      (fun w hw => by rcases Sym2.mem_iff.mp hw with h | h <;> rw [h] <;> assumption))
  have noP : ∀ y, (K.G.deleteEdges {s(p, z)}).Reachable z y → y ∉ cellNodes P := by
    intro y hy hyP
    have h1 : s(p, z) ∉ (K.path y p).edges := fun h =>
      hzP (path_inside K cellNodes hconn hyP hp _ h z (Sym2.mem_mk_right _ _))
    have h2 : (K.G.deleteEdges {s(p, z)}).Reachable y p := by
      by_contra hh
      exact h1 ((WT.mem_path_edges K y p _).mpr hh)
    exact not_reach_of_adj K.isTree.isAcyclic hpz (hy.trans h2).symm
  obtain ⟨c, hzc, hleaf⟩ := exists_leaf_behind K.isTree hpz
  refine ⟨c, hleaf, noP c hzc, ?_⟩
  obtain ⟨Wd⟩ := hzc.symm
  have hfree : ∀ e ∈ ((Wd.mapLe (K.G.deleteEdges_le _)).concat hpz.symm).edges,
      ¬ Inside cellNodes P e := by
    intro e he hin
    rw [Walk.edges_concat, Walk.edges_mapLe_eq_edges, List.concat_eq_append, List.mem_append,
      List.mem_singleton] at he
    rcases he with he | rfl
    · induction e with
      | _ e₁ e₂ =>
        have hs := Wd.fst_mem_support_of_mem_edges he
        exact noP e₁ (hzc.trans ⟨Wd.takeUntil e₁ hs⟩) (hin e₁ (Sym2.mem_mk_left _ _))
    · exact hzP (hin z (Sym2.mem_mk_left _ _))
  exact isProj_unique K cellNodes hconn (proj_spec K cellNodes ⟨p, hp⟩ c) ⟨hp, _, hfree⟩

end Hyp

end MTSPGL


/-!
# Claim 6.1 (Azarmehr–Behnezhad, *Metric TSP in Sublinear Time*, §6): gluing local solutions

Local Steiner trees `t P` of the cells `P` of the core, satisfying the cell distance constraints (9), have total
weight at most the cut LP value `K`. Instead of gluing explicitly, we build the dual of the glued tree directly:
every edge `f` of every `t P` gives the cut of the points whose anchor in `t P` lies on the far side of `f`, where
the anchor of a point `v` in `t P` is `ev P v` if `v` belongs to `P`, and otherwise the port of `P` through which
`q v` is reached (the projection of `q v` onto `P`). Then weak duality.
-/

open scoped Classical

namespace MTSPGL
open SimpleGraph TreeCoverLB MetricTSPSublinear

variable {n m : ℕ} (d : Fin n → Fin n → ℝ) (K : WeightedTree (Fin m)) (q : Fin n → Fin m)
  {ι : Type*} (cellNodes : ι → Finset (Fin m)) (cell : Fin n → ι) {mm : ι → ℕ}
  (t : ∀ P, WeightedTree (Fin (mm P))) (ev : ∀ P, Fin n → Fin (mm P)) (ep : ∀ P, Fin m → Fin (mm P))

/-- The anchor of the point `v` in the local tree `t P`. -/
noncomputable def anchor (P : ι) (v : Fin n) : Fin (mm P) :=
  if cell v = P then ev P v else ep P (proj K cellNodes P (q v))

/-- The cut given by the edge `f` of `t P`: the points anchored on the side of `f` away from `v₀`. -/
noncomputable def sideCut (v₀ : Fin n) (P : ι) (f : Sym2 (Fin (mm P))) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ¬ ((t P).G.deleteEdges {f}).Reachable
    (anchor K q cellNodes cell ev ep P v₀) (anchor K q cellNodes cell ev ep P v))

/-- The dual solution: `y_A` is the total weight of the local-tree edges whose cut is `A`. -/
noncomputable def dualY [Fintype ι] (v₀ : Fin n) (A : Finset (Fin n)) : ℝ :=
  ∑ P, ∑ f ∈ (t P).G.edgeFinset, if sideCut K q cellNodes cell t ev ep v₀ P f = A then (t P).w f else 0

lemma sum_dualY [Fintype ι] (v₀ : Fin n) :
    ∑ A, dualY K q cellNodes cell t ev ep v₀ A = ∑ P, ∑ f ∈ (t P).G.edgeFinset, (t P).w f := by
  unfold dualY
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [Finset.sum_ite_eq]
  simp

lemma sep_dualY [Fintype ι] (v₀ u v : Fin n) :
    ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => ¬ ((u ∈ A) ↔ (v ∈ A))),
        dualY K q cellNodes cell t ev ep v₀ A =
      ∑ P, (t P).dist (anchor K q cellNodes cell ev ep P u) (anchor K q cellNodes cell ev ep P v) := by
  unfold dualY
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Finset.sum_comm, WT.dist_eq_sum]
  refine Finset.sum_congr rfl (fun f hf => ?_)
  rw [Finset.sum_ite_eq]
  rw [mem_edgeFinset] at hf
  have hsep := WT.sep_iff (t P) (anchor K q cellNodes cell ev ep P v₀)
    (anchor K q cellNodes cell ev ep P u) (anchor K q cellNodes cell ev ep P v) hf
  have : sideCut K q cellNodes cell t ev ep v₀ P f ∈
      Finset.univ.filter (fun A : Finset (Fin n) => ¬ ((u ∈ A) ↔ (v ∈ A))) ↔
      f ∈ ((t P).path (anchor K q cellNodes cell ev ep P u) (anchor K q cellNodes cell ev ep P v)).edges := by
    rw [← hsep]
    simp [sideCut]
  by_cases h : f ∈ ((t P).path (anchor K q cellNodes cell ev ep P u)
      (anchor K q cellNodes cell ev ep P v)).edges
  · rw [if_pos (this.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]

section Hyp
variable (hconn : ∀ P, (K.G.induce (cellNodes P : Set (Fin m))).Preconnected)
  (hedge : ∀ a b, K.G.Adj a b → ∃! P, a ∈ cellNodes P ∧ b ∈ cellNodes P)
  (hcellEdge : ∀ P, ∃ a b, K.G.Adj a b ∧ a ∈ cellNodes P ∧ b ∈ cellNodes P)
  (hcell : ∀ v, q v ∈ cellNodes (cell v))
  (hleafK : ∀ c, (∀ y₁ y₂, K.G.Adj c y₁ → K.G.Adj c y₂ → y₁ = y₂) → ∃ s, q s = c)
  (hleafT : ∀ P c, (∀ y₁ y₂, (t P).G.Adj c y₁ → (t P).G.Adj c y₂ → y₁ = y₂) →
      (∃ v, cell v = P ∧ ev P v = c) ∨ (∃ p, IsPort cellNodes P p ∧ ep P p = c))
  (hq : ∀ u v, K.dist (q u) (q v) ≤ d u v)
  (h9a : ∀ P u v, cell u = P → cell v = P → (t P).dist (ev P u) (ev P v) ≤ d u v)
  (h9b : ∀ P v p, cell v = P → IsPort cellNodes P p → (t P).dist (ev P v) (ep P p) ≤ K.dist (q v) p)
  (h9c : ∀ P p p', IsPort cellNodes P p → IsPort cellNodes P p' →
      (t P).dist (ep P p) (ep P p') ≤ K.dist p p')

lemma cell_nonempty (hcellEdge : ∀ P, ∃ a b, K.G.Adj a b ∧ a ∈ cellNodes P ∧ b ∈ cellNodes P)
    (P : ι) : (cellNodes P).Nonempty := by
  obtain ⟨a, -, -, ha, -⟩ := hcellEdge P
  exact ⟨a, ha⟩

include hconn hedge hcellEdge hcell hleafK hleafT in
/-- Every leaf of a local tree is the anchor of some point. -/
lemma leaf_anchor (P : ι) (c : Fin (mm P))
    (hc : ∀ y₁ y₂, (t P).G.Adj c y₁ → (t P).G.Adj c y₂ → y₁ = y₂) :
    ∃ v, anchor K q cellNodes cell ev ep P v = c := by
  rcases hleafT P c hc with ⟨v, hv, hvc⟩ | ⟨p, hp, hpc⟩
  · exact ⟨v, by rw [anchor, if_pos hv, hvc]⟩
  · obtain ⟨c', hleaf, hc'P, hproj⟩ := exists_leaf_proj K cellNodes hconn hedge hp hcellEdge
    obtain ⟨s, hs⟩ := hleafK c' hleaf
    have hsP : cell s ≠ P := by
      intro h
      have := hcell s
      rw [h, hs] at this
      exact hc'P this
    exact ⟨s, by rw [anchor, if_neg hsP, hs, hproj, hpc]⟩

include hconn hedge hcellEdge hcell hq h9a h9b h9c in
/-- The separating weight of the dual for `u, v` is at most `d u v`. -/
lemma sum_anchor_le [Fintype ι] (u v : Fin n) :
    ∑ P, (t P).dist (anchor K q cellNodes cell ev ep P u) (anchor K q cellNodes cell ev ep P v) ≤
      d u v := by
  have hne := cell_nonempty K cellNodes hcellEdge
  by_cases huv : cell u = cell v
  · rw [Finset.sum_eq_single (cell u)]
    · rw [anchor, anchor, if_pos rfl, if_pos huv.symm]
      exact h9a _ u v rfl huv.symm
    · intro P _ hP
      rw [anchor, anchor, if_neg (Ne.symm hP), if_neg (huv ▸ Ne.symm hP),
        proj_eq_of_mem K cellNodes hconn hedge (Ne.symm hP) (hne P) (hcell u) (huv ▸ hcell v),
        WT.dist_self]
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine le_trans ?_ (le_trans (sum_dist_proj_le K cellNodes hconn hedge hne (q u) (q v)) (hq u v))
    refine Finset.sum_le_sum (fun P _ => ?_)
    unfold anchor
    by_cases hu : cell u = P
    · have hv : cell v ≠ P := fun hv => huv (hu.trans hv.symm)
      rw [if_pos hu, if_neg hv, proj_of_mem K cellNodes hconn (x := q u) (by rw [← hu]; exact hcell u)]
      exact h9b P u _ hu (proj_isPort K cellNodes hconn hedge hv (hne P) (hcell v))
    · by_cases hv : cell v = P
      · rw [if_neg hu, if_pos hv, proj_of_mem K cellNodes hconn (x := q v) (by rw [← hv]; exact hcell v),
          WT.dist_comm,
          WT.dist_comm K]
        exact h9b P v _ hv (proj_isPort K cellNodes hconn hedge hu (hne P) (hcell u))
      · rw [if_neg hu, if_neg hv]
        exact h9c P _ _ (proj_isPort K cellNodes hconn hedge hu (hne P) (hcell u))
          (proj_isPort K cellNodes hconn hedge hv (hne P) (hcell v))

include hconn hedge hcellEdge hcell hleafK hleafT hq h9a h9b h9c in
lemma dualY_feasible [Fintype ι] (v₀ : Fin n) :
    IsDualFeasible d Finset.univ (dualY K q cellNodes cell t ev ep v₀) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A
    unfold dualY
    refine Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun f hf => ?_))
    split_ifs
    · exact (t P).w_nonneg f (mem_edgeFinset.mp hf)
    · exact le_refl 0
  · intro A hA
    unfold dualY
    refine Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun f hf => ?_))
    rw [if_neg]
    rintro rfl
    apply hA
    refine ⟨Finset.subset_univ _, ?_, ?_⟩
    · obtain ⟨c, hc, hrc⟩ := WT.exists_leaf_side (t P) (anchor K q cellNodes cell ev ep P v₀)
        (mem_edgeFinset.mp hf)
      obtain ⟨v, hv⟩ := leaf_anchor K q cellNodes cell t ev ep hconn hedge hcellEdge hcell hleafK
        hleafT P c hc
      exact ⟨v, by simp [sideCut, hv, hrc]⟩
    · intro h
      have : v₀ ∈ sideCut K q cellNodes cell t ev ep v₀ P f := h ▸ Finset.mem_univ v₀
      simp [sideCut] at this
  · intro u _ v _ _
    rw [sep_dualY]
    exact sum_anchor_le d K q cellNodes cell t ev ep hconn hedge hcellEdge hcell hq h9a h9b h9c u v

end Hyp

/-- **Claim 6.1 (discrete form), with weak duality.** Local Steiner trees `t P` of the cells of the core `K`,
satisfying the cell distance constraints (9) (with `d_C = K.dist`), have total weight at most the cut LP value
`K = cutLP d univ`. -/
theorem glue_le_cutLP (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (K : WeightedTree (Fin m)) (q : Fin n → Fin m) (hq : ∀ u v, K.dist (q u) (q v) ≤ d u v)
    {ι : Type*} [Fintype ι] (cellNodes : ι → Finset (Fin m))
    (hconn : ∀ P, (K.G.induce (cellNodes P : Set (Fin m))).Preconnected)
    (hedge : ∀ a b, K.G.Adj a b → ∃! P, a ∈ cellNodes P ∧ b ∈ cellNodes P)
    (hcellEdge : ∀ P, ∃ a b, K.G.Adj a b ∧ a ∈ cellNodes P ∧ b ∈ cellNodes P)
    (cell : Fin n → ι) (hcell : ∀ v, q v ∈ cellNodes (cell v))
    (hleafK : ∀ c, (∀ y₁ y₂, K.G.Adj c y₁ → K.G.Adj c y₂ → y₁ = y₂) → ∃ s, q s = c)
    (mm : ι → ℕ) (t : ∀ P, WeightedTree (Fin (mm P)))
    (ev : ∀ P, Fin n → Fin (mm P)) (ep : ∀ P, Fin m → Fin (mm P))
    (h9a : ∀ P u v, cell u = P → cell v = P → (t P).dist (ev P u) (ev P v) ≤ d u v)
    (h9b : ∀ P v p, cell v = P → IsPort cellNodes P p →
      (t P).dist (ev P v) (ep P p) ≤ K.dist (q v) p)
    (h9c : ∀ P p p', IsPort cellNodes P p → IsPort cellNodes P p' →
      (t P).dist (ep P p) (ep P p') ≤ K.dist p p')
    (hleafT : ∀ P c, (∀ y₁ y₂, (t P).G.Adj c y₁ → (t P).G.Adj c y₂ → y₁ = y₂) →
      (∃ v, cell v = P ∧ ev P v = c) ∨ (∃ p, IsPort cellNodes P p ∧ ep P p = c)) :
    ∑ P, ∑ e ∈ (t P).G.edgeFinset, (t P).w e ≤ cutLP d Finset.univ := by
  by_cases hn : Nonempty (Fin n)
  · obtain ⟨v₀⟩ := hn
    rw [← sum_dualY K q cellNodes cell t ev ep v₀]
    exact cutLP_weak_duality d hd _ _
      (dualY_feasible d K q cellNodes cell t ev ep hconn hedge hcellEdge hcell hleafK hleafT hq
        h9a h9b h9c v₀)
  · -- no points: the local trees have no edges, and `0 ≤ cutLP` by weak duality for `y = 0`
    have h0 : ∀ P, ∑ e ∈ (t P).G.edgeFinset, (t P).w e = 0 := by
      intro P
      refine Finset.sum_eq_zero (fun f hf => ?_)
      exfalso
      have : Nonempty (Fin (mm P)) := ⟨(Quot.out f).1⟩
      obtain ⟨c, hc, -⟩ := WT.exists_leaf_side (t P) (Classical.arbitrary _ : Fin (mm P))
        (mem_edgeFinset.mp hf)
      obtain ⟨v, -⟩ := leaf_anchor K q cellNodes cell t ev ep hconn hedge hcellEdge hcell hleafK
        hleafT P c hc
      exact hn ⟨v⟩
    simp only [h0, Finset.sum_const_zero]
    have := cutLP_weak_duality d hd Finset.univ (fun _ => 0)
      ⟨fun _ => le_refl 0, fun _ _ => rfl, fun u _ => absurd ⟨u⟩ hn⟩
    simpa using this

end MTSPGL

open MetricTSPSublinear in
theorem solution {n m : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (K : TreeCoverLB.WeightedTree (Fin m)) (q : Fin n → Fin m) (hq : ∀ u v, K.dist (q u) (q v) ≤ d u v)
    {ι : Type*} [Fintype ι] (cellNodes : ι → Finset (Fin m))
    (hconn : ∀ P, (K.G.induce (cellNodes P : Set (Fin m))).Preconnected)
    (hedge : ∀ a b, K.G.Adj a b → ∃! P, a ∈ cellNodes P ∧ b ∈ cellNodes P)
    (hcellEdge : ∀ P, ∃ a b, K.G.Adj a b ∧ a ∈ cellNodes P ∧ b ∈ cellNodes P)
    (cell : Fin n → ι) (hcell : ∀ v, q v ∈ cellNodes (cell v))
    (hleafK : ∀ c, (∀ y₁ y₂, K.G.Adj c y₁ → K.G.Adj c y₂ → y₁ = y₂) → ∃ s, q s = c)
    (mm : ι → ℕ) (t : ∀ P, TreeCoverLB.WeightedTree (Fin (mm P)))
    (ev : ∀ P, Fin n → Fin (mm P)) (ep : ∀ P, Fin m → Fin (mm P))
    (h9a : ∀ P u v, cell u = P → cell v = P → (t P).dist (ev P u) (ev P v) ≤ d u v)
    (h9b : ∀ P v p, cell v = P → MetricTSPSublinear.IsPort cellNodes P p →
      (t P).dist (ev P v) (ep P p) ≤ K.dist (q v) p)
    (h9c : ∀ P p p', MetricTSPSublinear.IsPort cellNodes P p → MetricTSPSublinear.IsPort cellNodes P p' →
      (t P).dist (ep P p) (ep P p') ≤ K.dist p p')
    (hleafT : ∀ P c, (∀ y₁ y₂, (t P).G.Adj c y₁ → (t P).G.Adj c y₂ → y₁ = y₂) →
      (∃ v, cell v = P ∧ ev P v = c) ∨ (∃ p, MetricTSPSublinear.IsPort cellNodes P p ∧ ep P p = c)) :
    ∑ P, ∑ e ∈ (t P).G.edgeFinset, (t P).w e ≤ cutLP d Finset.univ :=
  MTSPGL.glue_le_cutLP d hd K q hq cellNodes hconn hedge hcellEdge cell hcell hleafK mm t ev ep h9a h9b h9c hleafT
