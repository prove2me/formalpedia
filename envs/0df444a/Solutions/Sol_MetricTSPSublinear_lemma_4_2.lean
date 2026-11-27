-- Prove2me | solution 1 for MetricTSPSublinear.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:03:43.376798+00:00
-- url     : https://prove2.me/submissions/2b179ee3-3c6e-4eb1-b38c-0ad3301510b4

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_IsDualFeasible
import Definitions.Def_MetricTSPSublinear_Dominated
import Definitions.Def_MetricTSPSublinear_dualOf


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


open MetricTSPSublinear

theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (S : Finset (Fin n)) (hS : S.Nonempty)
    (y : Finset (Fin n) → ℝ) (hy : IsDualFeasible d S y) :
    ∃ F : SteinerTree S, Dominated d F ∧ F.weight = ∑ A, y A :=
  MTSPL42.lemma_4_2_sol d hd S hS y hy
