-- Prove2me | solution 1 for MetricGenerators.ConnectedJoin.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:19:49.970791+00:00
-- url     : https://prove2.me/submissions/397bb668-b367-4519-82dd-73bb912f93f4

import Mathlib
import Definitions.Def_MetricGenerators_ConnectedJoin_TJoin
import Theorems.Thm_MetricGenerators_ConnectedJoin_minimal_tjoin_paths

open SimpleGraph MetricGenerators.FewComponents MetricGenerators.ConnectedJoin

namespace CJLemma2Aux

variable {V : Type*} [DecidableEq V]

theorem edgeDeg_sdiff {F D : Finset (Sym2 V)} (h : D ⊆ F) (v : V) :
    edgeDeg (F \ D) v + edgeDeg D v = edgeDeg F v := by
  unfold edgeDeg
  have : (F \ D).filter (fun e => v ∈ e) = F.filter (fun e => v ∈ e) \ D.filter (fun e => v ∈ e) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [this, Finset.card_sdiff_add_card_eq_card]
  exact Finset.filter_subset_filter _ h

theorem edgeDeg_symmDiff (X Y : Finset (Sym2 V)) (v : V) :
    edgeDeg (symmDiff X Y) v + 2 * edgeDeg (X ∩ Y) v = edgeDeg X v + edgeDeg Y v := by
  unfold edgeDeg
  have h1 : (symmDiff X Y).filter (fun e => v ∈ e) =
      symmDiff (X.filter (fun e => v ∈ e)) (Y.filter (fun e => v ∈ e)) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  have h2 : (X ∩ Y).filter (fun e => v ∈ e) =
      (X.filter (fun e => v ∈ e)) ∩ (Y.filter (fun e => v ∈ e)) := Finset.filter_inter_distrib _ _ _
  rw [h1, h2]
  set A := X.filter (fun e => v ∈ e)
  set B := Y.filter (fun e => v ∈ e)
  have hsd : symmDiff A B = (A ∪ B) \ (A ∩ B) := symmDiff_eq_sup_sdiff_inf _ _
  rw [hsd]
  have := Finset.card_union_add_card_inter A B
  have h3 := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_union (s := A) (t := B))
  omega

theorem card_symmDiff_le (X Y : Finset (Sym2 V)) :
    (symmDiff X Y).card ≤ X.card + Y.card := by
  have hsd : symmDiff X Y = (X ∪ Y) \ (X ∩ Y) := symmDiff_eq_sup_sdiff_inf _ _
  rw [hsd]
  exact Finset.card_le_card Finset.sdiff_subset |>.trans (Finset.card_union_le _ _)

/-- Parity of degrees in the edge set of a trail. -/
theorem trail_edgeDeg {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (hp : p.IsTrail) (x : V) :
    Even (edgeDeg p.edges.toFinset x) ↔ (u ≠ v → x ≠ u ∧ x ≠ v) := by
  rw [← hp.even_countP_edges_iff x, edgeDeg, List.filter_toFinset,
    List.toFinset_card_of_nodup (hp.edges_nodup.filter _), List.countP_eq_length_filter]

theorem walk_edges_subset {F : Finset (Sym2 V)} {a b : V} (w : (edgeGraph F).Walk a b) :
    w.edges.toFinset ⊆ F := by
  intro e he
  rw [List.mem_toFinset] at he
  have := w.edges_subset_edgeSet he
  simp only [edgeGraph, edgeSet_fromEdgeSet, Set.mem_sdiff, Finset.mem_coe] at this
  exact this.1

theorem edgeGraph_le {G : SimpleGraph V} {F : Finset (Sym2 V)}
    (hFG : (↑F : Set (Sym2 V)) ⊆ G.edgeSet) : edgeGraph F ≤ G := by
  intro a b h
  simp only [edgeGraph, fromEdgeSet_adj] at h
  exact hFG h.1

theorem hom_dist_le {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β} (f : A →g B)
    {a b : α} (h : A.Reachable a b) : B.dist (f a) (f b) ≤ A.dist a b := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  calc B.dist (f a) (f b) ≤ (p.map f).length := dist_le _
    _ = A.dist a b := by rw [Walk.length_map, hp]

theorem support_mem (F : Finset (Sym2 V)) {a b : V}
    (w : (edgeGraph F).Walk a b) (ha : a ∈ edgeSupport F) :
    ∀ z ∈ w.support, z ∈ edgeSupport F := by
  induction w with
  | nil => intro z hz; simp at hz; exact hz ▸ ha
  | @cons x y c h p ih =>
    have hy : y ∈ edgeSupport F := by
      simp only [edgeGraph, fromEdgeSet_adj] at h
      exact ⟨s(x, y), h.1, by simp⟩
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ha
    · exact ih hy z hz

theorem induce_dist (F : Finset (Sym2 V))
    (hconn : ((edgeGraph F).induce (edgeSupport F)).Connected)
    (x y : ↥(edgeSupport F)) :
    ((edgeGraph F).induce (edgeSupport F)).dist x y = (edgeGraph F).dist x.1 y.1 := by
  apply le_antisymm _ (hom_dist_le (Embedding.induce (edgeSupport F)).toHom (hconn x y))
  have hr : (edgeGraph F).Reachable x.1 y.1 :=
    (hconn x y).map (Embedding.induce (edgeSupport F)).toHom
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
  have hs := support_mem F w x.2
  have := dist_le (w.induce (edgeSupport F) hs)
  have hl : (w.induce (edgeSupport F) hs).length = w.length := by
    have := congrArg Walk.length (Walk.map_induce w hs)
    rw [Walk.length_map] at this
    exact this
  rw [hl, hw] at this
  exact this

/-- Necessity half of Lemma 2. -/
theorem lemma2_nec {G : SimpleGraph V} (hG : G.Connected)
    (T : Finset V) (F : Finset (Sym2 V)) (hconn : IsConnectedEdgeSet F)
    (hmin : IsMinTJoin G T F) :
    IsTreeEdgeSet F ∧ ∀ x ∈ edgeSupport F, ∀ y ∈ edgeSupport F, edgeDist F x y = G.dist x y := by
  classical
  have hTJ := hmin.1
  refine ⟨⟨hconn, ?_⟩, ?_⟩
  · intro v c hc
    set c' := c.map (Embedding.induce (edgeSupport F)).toHom with hc'
    have hc'cyc : c'.IsCycle :=
      (Walk.isCycle_map_iff_of_injective (Embedding.induce (G := edgeGraph F) (edgeSupport F)).injective).2 hc
    set C := c'.edges.toFinset
    have hCF : C ⊆ F := walk_edges_subset c'
    have hCne : C.Nonempty := by
      obtain ⟨e, he⟩ : ∃ e, e ∈ c'.edges := by
        rcases h : c'.edges with _ | ⟨e, _⟩
        · exact absurd (Walk.edges_eq_nil.1 h) hc'cyc.not_nil
        · exact ⟨e, by simp⟩
      exact ⟨e, List.mem_toFinset.2 he⟩
    have hJ : IsTJoin G T (F \ C) := by
      refine ⟨fun e he => hTJ.1 (Finset.mem_sdiff.1 he).1, fun w => ?_⟩
      rw [← hTJ.2 w]
      have h1 := edgeDeg_sdiff hCF w
      have h2 : Even (edgeDeg C w) := (trail_edgeDeg hc'cyc.isTrail w).2 (fun h => absurd rfl h)
      rw [← h1, Nat.odd_iff, Nat.odd_iff]
      rw [Nat.even_iff] at h2
      omega
    have := hmin.2 _ hJ
    have hlt : (F \ C).card < F.card :=
      Finset.card_lt_card (Finset.sdiff_ssubset hCF hCne)
    omega
  · intro x hx y hy
    have hFle := edgeGraph_le hTJ.1
    have hr : (edgeGraph F).Reachable x y :=
      (Connected.preconnected hconn ⟨x, hx⟩ ⟨y, hy⟩).map (Embedding.induce (edgeSupport F)).toHom
    have hle : G.dist x y ≤ edgeDist F x y := hom_dist_le (SimpleGraph.Hom.ofLE hFle) hr
    by_contra hne
    have hlt : G.dist x y < edgeDist F x y := lt_of_le_of_ne hle (Ne.symm hne)
    obtain ⟨P1, hP1, hP1l⟩ := hr.exists_path_of_dist
    obtain ⟨P2, hP2, hP2l⟩ := hG.exists_path_of_dist x y
    set E1 := P1.edges.toFinset
    set E2 := P2.edges.toFinset
    have hE1 : E1.card = edgeDist F x y := by
      rw [List.toFinset_card_of_nodup hP1.isTrail.edges_nodup, Walk.length_edges, hP1l]; rfl
    have hE2 : E2.card = G.dist x y := by
      rw [List.toFinset_card_of_nodup hP2.isTrail.edges_nodup, Walk.length_edges, hP2l]
    have hE1F : E1 ⊆ F := walk_edges_subset P1
    have hJ : IsTJoin G T (symmDiff (F \ E1) E2) := by
      refine ⟨fun e he => ?_, fun w => ?_⟩
      · rw [Finset.mem_coe, Finset.mem_symmDiff] at he
        rcases he with ⟨he, _⟩ | ⟨he, _⟩
        · exact hTJ.1 (Finset.mem_sdiff.1 he).1
        · exact P2.edges_subset_edgeSet (List.mem_toFinset.1 he)
      · rw [← hTJ.2 w]
        have h1 := edgeDeg_sdiff hE1F w
        have h2 := edgeDeg_symmDiff (F \ E1) E2 w
        have h3 := trail_edgeDeg hP1.isTrail w
        have h4 := trail_edgeDeg hP2.isTrail w
        have h34 : Even (edgeDeg E1 w) ↔ Even (edgeDeg E2 w) := h3.trans h4.symm
        rw [Nat.even_iff, Nat.even_iff] at h34
        rw [Nat.odd_iff, Nat.odd_iff]
        omega
    have h1 := hmin.2 _ hJ
    have h2 := card_symmDiff_le (F \ E1) E2
    have h3 := Finset.card_sdiff_add_card_eq_card hE1F
    have h4 : edgeDist F x y = (edgeGraph F).dist x y := rfl
    omega

/-- An acyclic finite graph in which every degree is even has no edge. -/
theorem no_edge_even_forest [Fintype V] (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : K.IsAcyclic) (heven : ∀ v, Even (K.degree v)) (u v : V) : ¬ K.Adj u v := by
  intro huv
  have hpath1 : (Walk.cons huv Walk.nil : K.Walk u v).IsPath :=
    Walk.IsPath.nil.cons (h := huv) (by simpa using huv.ne)
  have hex : ∃ n, ∃ (a b : V) (p : K.Walk a b), p.IsPath ∧ p.length = n := ⟨1, u, v, _, hpath1, rfl⟩
  have hbd : ∀ n, (∃ (a b : V) (p : K.Walk a b), p.IsPath ∧ p.length = n) → n ≤ Fintype.card V := by
    rintro n ⟨a, b, p, hp, rfl⟩
    exact (hp.length_lt).le
  classical
  obtain ⟨n, hn⟩ := hex
  let m := Nat.findGreatest (fun n => ∃ (a b : V) (p : K.Walk a b), p.IsPath ∧ p.length = n)
    (Fintype.card V)
  have hm : ∃ (a b : V) (p : K.Walk a b), p.IsPath ∧ p.length = m :=
    Nat.findGreatest_spec (P := fun n => ∃ (a b : V) (p : K.Walk a b), p.IsPath ∧ p.length = n)
      (hbd n hn) hn
  have hmax : ∀ k, (∃ (a b : V) (p : K.Walk a b), p.IsPath ∧ p.length = k) → k ≤ m :=
    fun k hk => Nat.le_findGreatest (hbd k hk) hk
  obtain ⟨a, b, p, hp, hpl⟩ := hm
  have hm1 : 1 ≤ m := hmax 1 ⟨u, v, _, hpath1, rfl⟩
  have hpnil : ¬ p.Nil := by
    rw [← Walk.length_eq_zero_iff]; omega
  have hadj : K.Adj a p.snd := Walk.adj_snd hpnil
  have hdeg0 : 0 < K.degree a := by
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.2 ⟨p.snd, by simpa using hadj⟩
  have hdeg : K.degree a ≠ 1 := by
    intro h; have := heven a; rw [h] at this; exact (Nat.not_even_one) this
  obtain ⟨w, hw, hwne⟩ : ∃ w ∈ K.neighborFinset a, w ≠ p.snd := by
    by_contra hcon
    push Not at hcon
    have : K.neighborFinset a ⊆ {p.snd} := fun x hx => by simpa using hcon x hx
    have := Finset.card_le_card this
    rw [card_neighborFinset_eq_degree] at this
    simp at this; omega
  rw [mem_neighborFinset] at hw
  by_cases hws : w ∈ p.support
  · have hwa : w ≠ a := hw.ne.symm
    have h1 : (p.takeUntil w hws).IsPath := hp.takeUntil hws
    have h2 : (Walk.cons hw Walk.nil : K.Walk a w).IsPath :=
      Walk.IsPath.nil.cons (h := hw) (by simpa using hw.ne)
    have heq := (hK.subsingleton_path _ _).elim ⟨_, h1⟩ ⟨_, h2⟩
    rw [Subtype.mk.injEq] at heq
    have := congrArg Walk.snd heq
    rw [Walk.snd_takeUntil hwa, Walk.snd_cons] at this
    exact hwne this.symm
  · have hp' : (Walk.cons hw.symm p).IsPath := hp.cons hws
    have := hmax _ ⟨_, _, _, hp', rfl⟩
    simp at this; omega

theorem degree_edgeGraph {G : SimpleGraph V} (F : Finset (Sym2 V))
    (hFG : (↑F : Set (Sym2 V)) ⊆ G.edgeSet) (v : V) [Fintype ((edgeGraph F).neighborSet v)] :
    (edgeGraph F).degree v = edgeDeg F v := by
  classical
  rw [← card_neighborFinset_eq_degree, edgeDeg]
  refine Finset.card_bij (fun w _ => s(v, w)) ?_ ?_ ?_
  · intro w hw
    rw [mem_neighborFinset] at hw
    simp only [edgeGraph, fromEdgeSet_adj] at hw
    exact Finset.mem_filter.2 ⟨Finset.mem_coe.1 hw.1, by simp⟩
  · intro a _ b _ hab
    exact Sym2.congr_right.1 hab
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 he.2
    have hne : v ≠ w := by
      intro h
      apply G.not_isDiag_of_mem_edgeSet (hFG he.1)
      simp [h]
    refine ⟨w, ?_, rfl⟩
    rw [mem_neighborFinset]
    simp only [edgeGraph, fromEdgeSet_adj]
    exact ⟨he.1, hne⟩

theorem even_card_of_tjoin [Fintype V] {G : SimpleGraph V} {T : Finset V} {F : Finset (Sym2 V)}
    (hF : IsTJoin G T F) : Even T.card := by
  classical
  have h := (edgeGraph F).even_card_odd_degree_vertices
  convert h using 2
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [degree_edgeGraph F hF.1 v, hF.2 v]

/-- Sufficiency half of Lemma 2. -/
theorem lemma2_suf [Fintype V] {G : SimpleGraph V} (hG : G.Connected)
    (T : Finset V) (F : Finset (Sym2 V)) (hF : IsTJoin G T F) (hconn : IsConnectedEdgeSet F)
    (htree : IsTreeEdgeSet F)
    (hdist : ∀ x ∈ edgeSupport F, ∀ y ∈ edgeSupport F, edgeDist F x y = G.dist x y) :
    IsMinTJoin G T F := by
  classical
  refine ⟨hF, fun J hJ => ?_⟩
  have hT : Even T.card := even_card_of_tjoin hF
  -- a minimal T-join inside J
  obtain ⟨J', hJ'mem, hJ'min⟩ := Finset.exists_min_image
    (J.powerset.filter (fun K => IsTJoin G T K)) Finset.card ⟨J, by simp [hJ]⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hJ'mem
  have hJ'minimal : IsMinimalTJoin G T J' := by
    refine ⟨hJ'mem.2, fun K hK hKT => ?_⟩
    have := hJ'min K (by
      rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hK.trans hJ'mem.1, hKT⟩)
    exact Finset.eq_of_subset_of_card_le hK this
  obtain ⟨s, t, P, hinj, hrange, hpath, hdisj, hunion⟩ :=
    minimal_tjoin_paths G hG T hT J' hJ'minimal
  -- T ⊆ V(F)
  have hTS : ∀ x ∈ T, x ∈ edgeSupport F := by
    intro x hx
    have hodd := (hF.2 x).2 hx
    have hpos : 0 < edgeDeg F x := hodd.pos
    rw [edgeDeg, Finset.card_pos] at hpos
    obtain ⟨e, he⟩ := hpos
    rw [Finset.mem_filter] at he
    exact ⟨e, he.1, he.2⟩
  have hsT : ∀ i, s i ∈ T := fun i => by
    have : Sum.elim s t (Sum.inl i) ∈ Set.range (Sum.elim s t) := ⟨_, rfl⟩
    rw [hrange] at this; exact this
  have htT : ∀ i, t i ∈ T := fun i => by
    have : Sum.elim s t (Sum.inr i) ∈ Set.range (Sum.elim s t) := ⟨_, rfl⟩
    rw [hrange] at this; exact this
  have hst : ∀ i, s i ≠ t i := fun i h => by
    have := hinj (a₁ := Sum.inl i) (a₂ := Sum.inr i) h
    exact Sum.inl_ne_inr this
  -- shortest paths in F
  have hreach : ∀ i, (edgeGraph F).Reachable (s i) (t i) := fun i =>
    (Connected.preconnected hconn ⟨s i, hTS _ (hsT i)⟩ ⟨t i, hTS _ (htT i)⟩).map
      (Embedding.induce (edgeSupport F)).toHom
  choose Q hQ hQl using fun i => (hreach i).exists_path_of_dist
  set EQ : Fin (T.card / 2) → Finset (Sym2 V) := fun i => (Q i).edges.toFinset with hEQ
  have hEQF : ∀ i, EQ i ⊆ F := fun i => walk_edges_subset (Q i)
  have hEQc : ∀ i, (EQ i).card = G.dist (s i) (t i) := by
    intro i
    rw [hEQ, List.toFinset_card_of_nodup (hQ i).isTrail.edges_nodup, Walk.length_edges, hQl i]
    exact hdist _ (hTS _ (hsT i)) _ (hTS _ (htT i))
  -- the chain |J| ≥ |J'| = Σ |P_i| ≥ Σ μ_G = Σ |Q_i|
  have hchain : ∑ i, (EQ i).card ≤ J.card := by
    calc ∑ i, (EQ i).card = ∑ i, G.dist (s i) (t i) := Finset.sum_congr rfl (fun i _ => hEQc i)
      _ ≤ ∑ i, (P i).edges.toFinset.card := by
        apply Finset.sum_le_sum; intro i _
        rw [List.toFinset_card_of_nodup (hpath i).isTrail.edges_nodup, Walk.length_edges]
        exact dist_le _
      _ = J'.card := by
        rw [← hunion, Finset.card_biUnion]
        intro i _ j _ hij; exact hdisj i j hij
      _ ≤ J.card := Finset.card_le_card hJ'mem.1
  -- multiplicity of each edge
  let c : Sym2 V → ℕ := fun e => (Finset.univ.filter (fun i => e ∈ EQ i)).card
  have hsum : ∑ i, (EQ i).card = ∑ e ∈ F, c e := by
    have : ∀ i, (EQ i).card = ∑ e ∈ F, if e ∈ EQ i then 1 else 0 := by
      intro i
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1; ext e; simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hEQF i h, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.sum_boole, Nat.cast_id]
  -- the odd-multiplicity edges form a T-join
  set F'' := F.filter (fun e => Odd (c e)) with hF''
  have hdegsum : ∀ v, ∑ e ∈ F.filter (fun e => v ∈ e), c e = ∑ i, edgeDeg (EQ i) v := by
    intro v
    have : ∀ i, edgeDeg (EQ i) v = ∑ e ∈ F.filter (fun e => v ∈ e), if e ∈ EQ i then 1 else 0 := by
      intro i
      rw [Finset.sum_boole, Nat.cast_id, edgeDeg]
      congr 1; ext e; simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨⟨hEQF i h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.sum_boole, Nat.cast_id]
  have hpar1 : ∀ (A : Finset (Sym2 V)), (∑ e ∈ A, c e) % 2 = (A.filter (fun e => Odd (c e))).card % 2 := by
    intro A
    rw [Finset.sum_nat_mod, Finset.card_filter]
    conv_rhs => rw [Finset.sum_nat_mod]
    congr 1
    apply Finset.sum_congr rfl; intro e _
    rcases Nat.even_or_odd (c e) with h | h
    · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]
    · rw [if_pos h, Nat.odd_iff.1 h]
  have hpar2 : ∀ v i, edgeDeg (EQ i) v % 2 = if v = s i ∨ v = t i then 1 else 0 := by
    intro v i
    have := trail_edgeDeg (hQ i).isTrail v
    split_ifs with h
    · have hne : ¬ Even (edgeDeg (EQ i) v) := by
        rw [this]; intro h'; have := h' (hst i); tauto
      exact Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hne)
    · have he : Even (edgeDeg (EQ i) v) := by
        rw [this]; intro _; push Not at h; exact h
      exact Nat.even_iff.1 he
  have hcount : ∀ v, (Finset.univ.filter (fun i : Fin (T.card / 2) => v = s i ∨ v = t i)).card =
      if v ∈ T then 1 else 0 := by
    intro v
    have hle : (Finset.univ.filter (fun i : Fin (T.card / 2) => v = s i ∨ v = t i)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact Sum.inl_injective (hinj (a₁ := Sum.inl i) (a₂ := Sum.inl j) (by simp [← hi, ← hj]))
      · exact absurd (hinj (a₁ := Sum.inl i) (a₂ := Sum.inr j) (by simp [← hi, ← hj])) Sum.inl_ne_inr
      · exact absurd (hinj (a₁ := Sum.inr i) (a₂ := Sum.inl j) (by simp [← hi, ← hj])) Sum.inr_ne_inl
      · exact Sum.inr_injective (hinj (a₁ := Sum.inr i) (a₂ := Sum.inr j) (by simp [← hi, ← hj]))
    split_ifs with hv
    · have : v ∈ Set.range (Sum.elim s t) := by rw [hrange]; exact hv
      obtain ⟨k, hk⟩ := this
      have hpos : 0 < (Finset.univ.filter (fun i : Fin (T.card / 2) => v = s i ∨ v = t i)).card := by
        rw [Finset.card_pos]
        rcases k with i | i
        · exact ⟨i, by simp [← hk]⟩
        · exact ⟨i, by simp [← hk]⟩
      omega
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro i - (h | h)
      · exact hv (h ▸ hsT i)
      · exact hv (h ▸ htT i)
  have hF''J : IsTJoin G T F'' := by
    refine ⟨fun e he => hF.1 (Finset.mem_filter.1 he).1, fun v => ?_⟩
    have h1 : edgeDeg F'' v = ((F.filter (fun e => v ∈ e)).filter (fun e => Odd (c e))).card := by
      rw [edgeDeg, hF'', Finset.filter_filter, Finset.filter_filter]
      congr 1; ext e; simp only [Finset.mem_filter]; tauto
    have h2 := hpar1 (F.filter (fun e => v ∈ e))
    rw [hdegsum v, ← h1] at h2
    have h3 : (∑ i, edgeDeg (EQ i) v) % 2 = (if v ∈ T then 1 else 0) % 2 := by
      rw [Finset.sum_nat_mod, Finset.sum_congr rfl (fun i _ => hpar2 v i), Finset.sum_boole,
        Nat.cast_id, hcount v]
    rw [Nat.odd_iff]
    split_ifs at h3 with hv <;> simp only [hv, iff_true, iff_false] <;> omega
  -- the even remainder F \ F'' lies in a forest, hence is empty
  have hF''F : F'' ⊆ F := Finset.filter_subset _ _
  have hD : F \ F'' = ∅ := by
    by_contra hne
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hacycF : (edgeGraph F).IsAcyclic := by
      intro v w hw
      have hv : v ∈ edgeSupport F := by
        have hadj := w.adj_snd hw.not_nil
        simp only [edgeGraph, fromEdgeSet_adj] at hadj
        exact ⟨_, hadj.1, by simp⟩
      have hs := support_mem F w hv
      have hc' : (w.induce (edgeSupport F) hs).IsCycle := by
        have h := hw
        rw [← Walk.map_induce w hs] at h
        exact (Walk.isCycle_map_iff_of_injective
          (Embedding.induce (G := edgeGraph F) (edgeSupport F)).injective).1 h
      exact htree.isAcyclic (w.induce (edgeSupport F) hs) hc'
    set D := F \ F''
    have hDle : edgeGraph D ≤ edgeGraph F := by
      intro a b h
      simp only [edgeGraph, fromEdgeSet_adj, Finset.mem_coe] at h ⊢
      exact ⟨(Finset.mem_sdiff.1 h.1).1, h.2⟩
    have hDG : (↑D : Set (Sym2 V)) ⊆ G.edgeSet := fun e he => hF.1 (Finset.mem_sdiff.1 he).1
    have heven : ∀ v, Even ((edgeGraph D).degree v) := by
      intro v
      rw [degree_edgeGraph D hDG v]
      have h1 : edgeDeg D v + edgeDeg F'' v = edgeDeg F v := edgeDeg_sdiff hF''F v
      have h2 := hF.2 v
      have h3 := hF''J.2 v
      rw [Nat.even_iff]
      simp only [Nat.odd_iff] at h2 h3
      by_cases hv : v ∈ T <;> simp only [hv, iff_true, iff_false] at h2 h3 <;> omega
    induction e using Sym2.ind with
    | _ a b =>
      have hab : (edgeGraph D).Adj a b := by
        simp only [edgeGraph, fromEdgeSet_adj, Finset.mem_coe]
        refine ⟨he, fun h => ?_⟩
        subst h
        exact G.not_isDiag_of_mem_edgeSet (hDG he) (by simp)
      exact no_edge_even_forest (edgeGraph D) (hacycF.anti hDle) heven a b hab
  -- every edge of F has odd, hence positive, multiplicity
  have hc1 : ∀ e ∈ F, 1 ≤ c e := by
    intro e he
    have : e ∈ F'' := by
      by_contra h
      have : e ∈ F \ F'' := Finset.mem_sdiff.2 ⟨he, h⟩
      rw [hD] at this; simp at this
    exact (Finset.mem_filter.1 this).2.pos
  have : F.card ≤ ∑ e ∈ F, c e := by
    rw [Finset.card_eq_sum_ones]; exact Finset.sum_le_sum hc1
  omega

end CJLemma2Aux

open CJLemma2Aux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : G.Connected)
    (T : Finset V) (F : Finset (Sym2 V)) (hF : MetricGenerators.FewComponents.IsTJoin G T F) (hconn : IsConnectedEdgeSet F) :
    MetricGenerators.FewComponents.IsMinTJoin G T F ↔
      IsTreeEdgeSet F ∧
        ∀ x ∈ MetricGenerators.FewComponents.edgeSupport F, ∀ y ∈ MetricGenerators.FewComponents.edgeSupport F, edgeDist F x y = G.dist x y :=
  ⟨fun h => lemma2_nec hG T F hconn h, fun h => lemma2_suf hG T F hF hconn h.1 h.2⟩
