-- Prove2me | solution 1 for MetricGenerators.ConnectedJoin.minimal_tjoin_paths
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:23:41.225538+00:00
-- url     : https://prove2.me/submissions/34f8c777-d5f8-4ddd-b5d6-b0ca5aaed96f

import Mathlib
import Definitions.Def_MetricGenerators_ConnectedJoin_TJoin

open SimpleGraph MetricGenerators.FewComponents MetricGenerators.ConnectedJoin

namespace CJPathsAux

variable {V : Type*} [DecidableEq V]

theorem edgeDeg_sdiff {F D : Finset (Sym2 V)} (h : D ⊆ F) (v : V) :
    edgeDeg (F \ D) v + edgeDeg D v = edgeDeg F v := by
  unfold edgeDeg
  have : (F \ D).filter (fun e => v ∈ e) = F.filter (fun e => v ∈ e) \ D.filter (fun e => v ∈ e) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [this, Finset.card_sdiff_add_card_eq_card]
  exact Finset.filter_subset_filter _ h

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

/-- In a `T`-join with `t0 ∈ T`, there is another vertex of `T` reachable from `t0` in `F`. -/
theorem exists_reach [Fintype V] {G : SimpleGraph V} {T : Finset V} {F : Finset (Sym2 V)}
    (hF : IsTJoin G T F) {t0 : V} (ht0 : t0 ∈ T) :
    ∃ t1 ∈ T, t1 ≠ t0 ∧ (edgeGraph F).Reachable t0 t1 := by
  classical
  set C : Set V := {w | (edgeGraph F).Reachable t0 w}
  set K := (edgeGraph F).induce C
  have hdeg : ∀ w : C, K.degree w = edgeDeg F w.1 := by
    intro w
    rw [← degree_edgeGraph F hF.1 w.1, ← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
    refine Fintype.card_congr
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun y => ⟨⟨y.1, w.2.trans y.2.reachable⟩, y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have h0 : Odd (K.degree ⟨t0, Reachable.refl _⟩) := by
    rw [hdeg]; exact (hF.2 t0).2 ht0
  obtain ⟨w, hw, hodd⟩ := K.exists_ne_odd_degree_of_exists_odd_degree _ h0
  rw [hdeg] at hodd
  refine ⟨w.1, (hF.2 w.1).1 hodd, fun h => hw (Subtype.ext h), w.2⟩

theorem main [Fintype V] (G : SimpleGraph V) (n : ℕ) :
    ∀ (T : Finset V) (F : Finset (Sym2 V)), T.card = 2 * n → IsMinimalTJoin G T F →
    ∃ (s t : Fin n → V) (P : ∀ i, G.Walk (s i) (t i)),
      Function.Injective (Sum.elim s t) ∧
      Set.range (Sum.elim s t) = (↑T : Set V) ∧
      (∀ i, (P i).IsPath) ∧
      (∀ i j, i ≠ j → Disjoint (P i).edges.toFinset (P j).edges.toFinset) ∧
      Finset.univ.biUnion (fun i => (P i).edges.toFinset) = F := by
  classical
  induction n with
  | zero =>
    intro T F hT hF
    have hT0 : T = ∅ := Finset.card_eq_zero.1 (by simpa using hT)
    subst hT0
    have hF0 : F = ∅ := by
      have h := hF.2 ∅ (Finset.empty_subset _) ⟨by simp, fun v => by simp [edgeDeg]⟩
      exact h.symm
    subst hF0
    refine ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, ?_, ?_, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, by simp⟩
    · intro a; rcases a with a | a <;> exact Fin.elim0 a
    · ext x; simp only [Finset.coe_empty, Set.mem_empty_iff_false, iff_false]
      rintro ⟨a, _⟩; rcases a with a | a <;> exact Fin.elim0 a
  | succ n ih =>
    intro T F hT hF
    have hTJ := hF.1
    obtain ⟨t0, ht0⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨t1, ht1, ht10, hr⟩ := exists_reach hTJ ht0
    obtain ⟨Q, hQ, -⟩ := hr.exists_path_of_dist
    set P0 : G.Walk t0 t1 := Q.mapLe (edgeGraph_le hTJ.1)
    have hP0 : P0.IsPath := hQ.mapLe _
    set E := P0.edges.toFinset with hE
    have hEeq : E = Q.edges.toFinset := by rw [hE, Walk.edges_mapLe_eq_edges]
    have hEF : E ⊆ F := hEeq ▸ walk_edges_subset Q
    have hEdeg : ∀ v, Odd (edgeDeg E v) ↔ (v = t0 ∨ v = t1) := by
      intro v
      rw [← Nat.not_even_iff_odd, trail_edgeDeg hP0.isTrail v]
      constructor
      · intro h; by_contra h'; push Not at h'; exact h (fun _ => h')
      · intro h h'; have := h' (Ne.symm ht10); tauto
    set T1 := (T.erase t0).erase t1 with hT1
    set F1 := F \ E with hF1
    have hT1card : T1.card = 2 * n := by
      rw [hT1, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨ht10, ht1⟩),
        Finset.card_erase_of_mem ht0]
      omega
    have hF1J : IsTJoin G T1 F1 := by
      refine ⟨fun e he => hTJ.1 (Finset.mem_sdiff.1 he).1, fun v => ?_⟩
      have h1 : edgeDeg F1 v + edgeDeg E v = edgeDeg F v := edgeDeg_sdiff hEF v
      have h2 := hTJ.2 v
      have h3 := hEdeg v
      simp only [hT1, Finset.mem_erase]
      simp only [Nat.odd_iff] at h2 h3 ⊢
      by_cases hv0 : v = t0
      · subst hv0; simp only [true_or, iff_true] at h3
        simp only [ht0, iff_true] at h2
        simp only [Ne.symm ht10, ne_eq, not_true_eq_false, and_false, false_and, iff_false]
        omega
      · by_cases hv1 : v = t1
        · subst hv1; simp only [or_true, iff_true] at h3
          simp only [ht1, iff_true] at h2
          simp only [ne_eq, not_true_eq_false, false_and, iff_false]
          omega
        · simp only [hv0, hv1, or_self, iff_false] at h3
          simp only [ne_eq, hv0, hv1, not_false_eq_true, true_and]
          constructor
          · intro h; exact h2.1 (by omega)
          · intro h; have := h2.2 h; omega
    have hF1min : IsMinimalTJoin G T1 F1 := by
      refine ⟨hF1J, fun K hK hKJ => ?_⟩
      have hdisj : Disjoint K E := by
        rw [Finset.disjoint_left]; intro e heK heE
        exact (Finset.mem_sdiff.1 (hK heK)).2 heE
      have hKE : IsTJoin G T (K ∪ E) := by
        refine ⟨fun e he => ?_, fun v => ?_⟩
        · rcases Finset.mem_union.1 he with h | h
          · exact hTJ.1 (Finset.mem_sdiff.1 (hK h)).1
          · exact hTJ.1 (hEF h)
        · have h1 := edgeDeg_sdiff (F := K ∪ E) (D := E) Finset.subset_union_right v
          rw [Finset.union_sdiff_cancel_right hdisj] at h1
          have h2 := hKJ.2 v
          have h3 := hEdeg v
          rw [← h1]
          simp only [hT1, Finset.mem_erase] at h2
          simp only [Nat.odd_iff] at h2 h3 ⊢
          by_cases hv0 : v = t0
          · subst hv0; simp only [true_or, iff_true] at h3
            simp only [Ne.symm ht10, ne_eq, not_true_eq_false, and_false, false_and, iff_false] at h2
            simp only [ht0, iff_true]; omega
          · by_cases hv1 : v = t1
            · subst hv1; simp only [or_true, iff_true] at h3
              simp only [ne_eq, not_true_eq_false, false_and, iff_false] at h2
              simp only [ht1, iff_true]; omega
            · simp only [hv0, hv1, or_self, iff_false] at h3
              simp only [ne_eq, hv0, hv1, not_false_eq_true, true_and] at h2
              constructor
              · intro h; exact h2.1 (by omega)
              · intro h; have := h2.2 h; omega
      have hsub : K ∪ E ⊆ F := Finset.union_subset (fun e he => (Finset.mem_sdiff.1 (hK he)).1) hEF
      have heq := hF.2 _ hsub hKE
      rw [hF1, ← heq, Finset.union_sdiff_cancel_right hdisj]
    obtain ⟨s', t', P', hinj', hrange', hpath', hdisj', hunion'⟩ := ih T1 F1 hT1card hF1min
    have hs'T : ∀ i, s' i ∈ T1 := fun i => by
      have : Sum.elim s' t' (Sum.inl i) ∈ Set.range (Sum.elim s' t') := ⟨_, rfl⟩
      rw [hrange'] at this; exact this
    have ht'T : ∀ i, t' i ∈ T1 := fun i => by
      have : Sum.elim s' t' (Sum.inr i) ∈ Set.range (Sum.elim s' t') := ⟨_, rfl⟩
      rw [hrange'] at this; exact this
    have hmemT1 : ∀ x, x ∈ T1 ↔ x ≠ t1 ∧ x ≠ t0 ∧ x ∈ T := by
      intro x; simp [hT1, Finset.mem_erase]
    have hP'F1 : ∀ i, (P' i).edges.toFinset ⊆ F1 := by
      intro i e he; rw [← hunion']; exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, he⟩
    refine ⟨Fin.cons t0 s', Fin.cons t1 t', fun i => Fin.cases P0 (fun j => P' j) i,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      rcases a with i | i <;> rcases b with j | j <;>
        (induction i using Fin.cases <;> induction j using Fin.cases) <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Fin.cons_zero, Fin.cons_succ] at hab
      all_goals first
        | rfl
        | (exact absurd hab ht10.symm)
        | (exact absurd hab ht10)
        | (exact absurd hab.symm ((hmemT1 _).1 (hs'T _)).2.1)
        | (exact absurd hab ((hmemT1 _).1 (hs'T _)).2.1)
        | (exact absurd hab.symm ((hmemT1 _).1 (ht'T _)).2.1)
        | (exact absurd hab ((hmemT1 _).1 (ht'T _)).2.1)
        | (exact absurd hab.symm ((hmemT1 _).1 (hs'T _)).1)
        | (exact absurd hab ((hmemT1 _).1 (hs'T _)).1)
        | (exact absurd hab.symm ((hmemT1 _).1 (ht'T _)).1)
        | (exact absurd hab ((hmemT1 _).1 (ht'T _)).1)
        | (have := hinj' (a₁ := Sum.inl _) (a₂ := Sum.inl _) hab; simp_all)
        | (have := hinj' (a₁ := Sum.inl _) (a₂ := Sum.inr _) hab; simp_all)
        | (have := hinj' (a₁ := Sum.inr _) (a₂ := Sum.inl _) hab; simp_all)
        | (have := hinj' (a₁ := Sum.inr _) (a₂ := Sum.inr _) hab; simp_all)
    · ext x
      simp only [Set.mem_range, Finset.mem_coe]
      constructor
      · rintro ⟨a, rfl⟩
        rcases a with i | i <;> induction i using Fin.cases <;>
          simp only [Sum.elim_inl, Sum.elim_inr, Fin.cons_zero, Fin.cons_succ]
        · exact ht0
        · exact ((hmemT1 _).1 (hs'T _)).2.2
        · exact ht1
        · exact ((hmemT1 _).1 (ht'T _)).2.2
      · intro hx
        by_cases hx0 : x = t0
        · exact ⟨Sum.inl 0, by simp [hx0]⟩
        by_cases hx1 : x = t1
        · exact ⟨Sum.inr 0, by simp [hx1]⟩
        have : x ∈ Set.range (Sum.elim s' t') := by
          rw [hrange']; exact (hmemT1 x).2 ⟨hx1, hx0, hx⟩
        obtain ⟨a, ha⟩ := this
        rcases a with i | i
        · exact ⟨Sum.inl i.succ, by simpa using ha⟩
        · exact ⟨Sum.inr i.succ, by simpa using ha⟩
    · intro i
      induction i using Fin.cases
      · exact hP0
      · exact hpath' _
    · intro i j hij
      induction i using Fin.cases <;> induction j using Fin.cases
      · exact absurd rfl hij
      · simp only [Fin.cases_zero, Fin.cases_succ]
        rw [Finset.disjoint_left]
        intro e he he'
        exact (Finset.mem_sdiff.1 (hP'F1 _ he')).2 he
      · simp only [Fin.cases_zero, Fin.cases_succ]
        rw [Finset.disjoint_left]
        intro e he he'
        exact (Finset.mem_sdiff.1 (hP'F1 _ he)).2 he'
      · simp only [Fin.cases_succ]
        exact hdisj' _ _ (fun h => hij (congrArg Fin.succ h))
    · ext e
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        induction i using Fin.cases
        · exact hEF hi
        · exact (Finset.mem_sdiff.1 (hP'F1 _ hi)).1
      · intro he
        by_cases heE : e ∈ E
        · exact ⟨0, heE⟩
        · have : e ∈ F1 := Finset.mem_sdiff.2 ⟨he, heE⟩
          rw [← hunion', Finset.mem_biUnion] at this
          obtain ⟨j, _, hj⟩ := this
          exact ⟨j.succ, hj⟩

end CJPathsAux

open CJPathsAux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) (T : Finset V) (hT : Even T.card) (F : Finset (Sym2 V))
    (hF : IsMinimalTJoin G T F) :
    ∃ (s t : Fin (T.card / 2) → V) (P : ∀ i, G.Walk (s i) (t i)),
      Function.Injective (Sum.elim s t) ∧
      Set.range (Sum.elim s t) = (↑T : Set V) ∧
      (∀ i, (P i).IsPath) ∧
      (∀ i j, i ≠ j → Disjoint (P i).edges.toFinset (P j).edges.toFinset) ∧
      Finset.univ.biUnion (fun i => (P i).edges.toFinset) = F :=
  main G (T.card / 2) T F (by obtain ⟨k, hk⟩ := hT; omega) hF
