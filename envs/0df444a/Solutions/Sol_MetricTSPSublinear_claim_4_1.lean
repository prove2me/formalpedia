-- Prove2me | solution 1 for MetricTSPSublinear.claim_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:53:47.105686+00:00
-- url     : https://prove2.me/submissions/4be02e39-eb37-4804-ac7a-d69cbce7d6b1

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


open MetricTSPSublinear

theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (S : Finset (Fin n)) (F : SteinerTree S)
    (x₀ : Fin n) (hx₀ : x₀ ∈ S) :
    IsDualFeasible d S (dualOf F x₀) ↔ Dominated d F :=
  MTSPSteiner.claim_4_1_sol d hd F x₀ hx₀
