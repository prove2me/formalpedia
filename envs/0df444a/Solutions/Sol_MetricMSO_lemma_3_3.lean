-- Prove2me | solution 1 for MetricMSO.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T05:01:05.641097+00:00
-- url     : https://prove2.me/submissions/ab04e632-abfc-4381-a3f5-46623f738a76

import Mathlib
import Definitions.Def_MetricMSO_cbl
import Definitions.Def_MetricMSO_signedSum

open MetricMSO

namespace Aux33

open Classical

noncomputable def edgesOf {V : Type} [Fintype V] (H : SimpleGraph V) : Finset (Sym2 V) :=
  Finset.univ.filter (fun e => e ∈ H.edgeSet)

lemma mem_edgesOf {V : Type} [Fintype V] {H : SimpleGraph V} {e : Sym2 V} :
    e ∈ edgesOf H ↔ e ∈ H.edgeSet := by
  simp [edgesOf]

lemma zmod2_neg_eq (z : ZMod 2) : -z = z := by
  revert z; decide

lemma signedSum_potential {V : Type} {G : SimpleGraph V} {O : V → V → Prop}
    (hO : IsRefOrientation G O) (δ : Sym2 V → ℤ) (lam : V → ℤ)
    (hlam : ∀ u v, O u v → lam v - lam u = δ s(u, v)) :
    ∀ {x y : V} (W : G.Walk x y), signedSum O δ W = lam y - lam x
  | _, _, .nil => by simp [signedSum]
  | x, y, @SimpleGraph.Walk.cons _ _ _ w _ hadj p => by
    rw [signedSum, signedSum_potential hO δ lam hlam p]
    by_cases hxw : O x w
    · rw [if_pos hxw, ← hlam x w hxw]; ring
    · have hwx : O w x := by
        have := hO.2 w x hadj.symm
        tauto
      rw [if_neg hxw, Sym2.eq_swap, ← hlam w x hwx]; ring

lemma signedSum_sub {V : Type} {G : SimpleGraph V} (O : V → V → Prop) (δ₁ δ₂ : Sym2 V → ℤ) :
    ∀ {x y : V} (W : G.Walk x y),
      signedSum O (fun e => δ₁ e - δ₂ e) W = signedSum O δ₁ W - signedSum O δ₂ W
  | _, _, .nil => by simp [signedSum]
  | x, _, @SimpleGraph.Walk.cons _ _ _ w _ _ p => by
    rw [signedSum, signedSum, signedSum, signedSum_sub O δ₁ δ₂ p]
    by_cases hxw : O x w <;> simp [hxw] <;> ring

lemma signedSum_two_mul {V : Type} {G : SimpleGraph V} (O : V → V → Prop) (b b' : Sym2 V → ℤ)
    (hb : ∀ e ∈ G.edgeSet, b e = 2 * b' e) :
    ∀ {x y : V} (W : G.Walk x y), signedSum O b W = 2 * signedSum O b' W
  | _, _, .nil => by simp [signedSum]
  | x, _, @SimpleGraph.Walk.cons _ _ _ w _ hadj p => by
    rw [signedSum, signedSum, signedSum_two_mul O b b' hb p]
    have he : s(x, w) ∈ G.edgeSet := hadj
    rw [hb s(x, w) he]
    by_cases hxw : O x w <;> simp [hxw] <;> ring

lemma signedSum_cast_zmod2 {V : Type} {G : SimpleGraph V} (O : V → V → Prop) (b : Sym2 V → ℤ) :
    ∀ {x y : V} (W : G.Walk x y),
      (signedSum O b W : ZMod 2) = (W.edges.map fun e => (b e : ZMod 2)).sum
  | _, _, .nil => by simp [signedSum]
  | x, _, @SimpleGraph.Walk.cons _ _ _ w _ _ p => by
    rw [signedSum, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
      ← signedSum_cast_zmod2 O b p]
    push_cast
    congr 1
    by_cases hxw : O x w
    · simp [hxw]
    · simp only [hxw, ↓reduceIte]
      exact zmod2_neg_eq _

lemma path_length_lt_card {V : Type} [Fintype V] {T : SimpleGraph V} {u v : V}
    {p : T.Walk u v} (hp : p.IsPath) : p.length < Fintype.card V := by
  have h1 : p.support.length ≤ Fintype.card V := hp.support_nodup.length_le_card
  rw [SimpleGraph.Walk.length_support] at h1
  omega

lemma exists_isPath_of_reachable {V : Type} {T : SimpleGraph V} {u v : V}
    (h : T.Reachable u v) : ∃ p : T.Walk u v, p.IsPath := by
  obtain ⟨w⟩ := h
  exact ⟨w.bypass, w.bypass_isPath⟩

lemma exists_leaf_of_acyclic {V : Type} [Fintype V] {T : SimpleGraph V}
    (hacyc : T.IsAcyclic) (hne : 0 < (edgesOf T).card) :
    ∃ a w : V, T.Adj a w ∧ ∀ z, T.Adj a z → z = w := by
  have hex_edge : ∃ x₀ y₀ : V, T.Adj x₀ y₀ := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hne
    rw [mem_edgesOf] at he
    induction e using Sym2.ind with
    | _ x₀ y₀ => exact ⟨x₀, y₀, he⟩
  obtain ⟨x₀, y₀, hadj₀⟩ := hex_edge
  let P : ℕ → Prop := fun l => ∃ (u v : V) (p : T.Walk u v), p.IsPath ∧ p.length = l
  let S : Finset ℕ := (Finset.range (Fintype.card V)).filter P
  have h1_mem : 1 ∈ S := by
    rw [Finset.mem_filter, Finset.mem_range]
    let p₀ : T.Walk x₀ y₀ := SimpleGraph.Walk.cons hadj₀ .nil
    have hp₀ : p₀.IsPath :=
      SimpleGraph.Walk.IsPath.cons (by simp) (by simp [T.ne_of_adj hadj₀])
    exact ⟨path_length_lt_card hp₀, x₀, y₀, p₀, hp₀, rfl⟩
  obtain ⟨L, hL_mem, hL_max⟩ := Finset.exists_max_image S id ⟨1, h1_mem⟩
  have hL_ge : 1 ≤ L := hL_max 1 h1_mem
  obtain ⟨_, a, b, p, hp, hpL⟩ := Finset.mem_filter.mp hL_mem
  cases p with
  | nil => simp at hpL; omega
  | @cons _ w _ hadj_aw q =>
    refine ⟨a, w, hadj_aw, ?_⟩
    intro z hadj_az
    by_contra hzw
    have hza : z ≠ a := (T.ne_of_adj hadj_az).symm
    by_cases hz_mem : z ∈ (SimpleGraph.Walk.cons hadj_aw q).support
    · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz_mem
      rcases hz_mem with rfl | hz_q
      · exact hza rfl
      · have hp_cons := (SimpleGraph.Walk.cons_isPath_iff hadj_aw q).mp hp
        have hq_path : q.IsPath := hp_cons.1
        have ha_not_q : a ∉ q.support := hp_cons.2
        let r₀ : T.Walk w z := q.takeUntil z hz_q
        have hr₀_path : r₀.IsPath := hq_path.takeUntil hz_q
        have ha_not_r₀ : a ∉ r₀.support := fun ha =>
          ha_not_q (SimpleGraph.Walk.support_takeUntil_subset q hz_q ha)
        let p₁ : T.Walk a z := SimpleGraph.Walk.cons hadj_aw r₀
        have hp₁_path : p₁.IsPath := (SimpleGraph.Walk.cons_isPath_iff hadj_aw r₀).mpr
          ⟨hr₀_path, ha_not_r₀⟩
        have hnot_edges : s(z, a) ∉ p₁.edges := by
          simp only [p₁, SimpleGraph.Walk.edges_cons, List.mem_cons, not_or]
          refine ⟨?_, ?_⟩
          · intro heq
            rw [Sym2.eq_iff] at heq
            rcases heq with ⟨rfl, _⟩ | ⟨rfl, _⟩
            · exact hza rfl
            · exact hzw rfl
          · intro hmem
            exact ha_not_r₀ (SimpleGraph.Walk.snd_mem_support_of_mem_edges r₀ hmem)
        have hcyc : (SimpleGraph.Walk.cons hadj_az.symm p₁).IsCycle :=
          (SimpleGraph.Walk.cons_isCycle_iff p₁ hadj_az.symm).mpr ⟨hp₁_path, hnot_edges⟩
        exact hacyc _ hcyc
    · let p' : T.Walk z b := SimpleGraph.Walk.cons hadj_az.symm (SimpleGraph.Walk.cons hadj_aw q)
      have hp'_path : p'.IsPath :=
        (SimpleGraph.Walk.cons_isPath_iff hadj_az.symm _).mpr ⟨hp, hz_mem⟩
      have hsucc_mem : L + 1 ∈ S := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by simpa [p', hpL] using path_length_lt_card hp'_path,
          z, b, p', hp'_path, by simp [p', hpL]⟩
      have hle_L : L + 1 ≤ L := hL_max (L + 1) hsucc_mem
      omega

lemma exists_potential_on_acyclic {V : Type} [Fintype V] {G : SimpleGraph V}
    {O : V → V → Prop} (hO : IsRefOrientation G O) (δ : Sym2 V → ℤ) :
    ∀ (n : ℕ) (T : SimpleGraph V), (edgesOf T).card = n → T ≤ G → T.IsAcyclic →
      ∃ lam : V → ℤ, ∀ u v, T.Adj u v → O u v → lam v - lam u = δ s(u, v) := by
  intro n
  induction n with
  | zero =>
    intro T hcard _ _
    refine ⟨fun _ => 0, fun u v hadj _ => ?_⟩
    have hmem : s(u, v) ∈ edgesOf T := mem_edgesOf.mpr hadj
    rw [Finset.card_eq_zero.mp hcard] at hmem
    exact False.elim (Finset.notMem_empty _ hmem)
  | succ n ih =>
    intro T hcard hT_le hT_acyc
    obtain ⟨a, w, hadj_aw, huniq⟩ := exists_leaf_of_acyclic hT_acyc (by omega)
    let T' : SimpleGraph V := T.deleteEdges {s(a, w)}
    have hT'_le_T : T' ≤ T := SimpleGraph.deleteEdges_le _
    have hT'_acyc : T'.IsAcyclic := fun v c hc =>
      hT_acyc (c.transfer T fun e he => SimpleGraph.edgeSet_mono hT'_le_T (c.edges_subset_edgeSet he))
        (hc.transfer _)
    have hT'_card : (edgesOf T').card = n := by
      have heq : edgesOf T' = (edgesOf T).erase s(a, w) := by
        ext e
        simp only [mem_edgesOf, Finset.mem_erase, ne_eq]
        induction e using Sym2.ind with
        | _ x y => simp [T', SimpleGraph.deleteEdges_adj, and_comm]
      have haw_mem : s(a, w) ∈ edgesOf T := mem_edgesOf.mpr hadj_aw
      rw [heq, Finset.card_erase_of_mem haw_mem, hcard]
      rfl
    obtain ⟨lam', hlam'⟩ := ih T' hT'_card (hT'_le_T.trans hT_le) hT'_acyc
    let val_a : ℤ := if O a w then lam' w - δ s(a, w) else lam' w + δ s(a, w)
    let lam : V → ℤ := fun x => if x = a then val_a else lam' x
    refine ⟨lam, fun u v hadj houv => ?_⟩
    have haw_ne : a ≠ w := T.ne_of_adj hadj_aw
    rcases eq_or_ne u a with rfl | hua
    · have hvw : v = w := huniq v hadj
      rcases hvw with rfl
      simp [lam, haw_ne.symm, val_a, houv]
    · rcases eq_or_ne v a with rfl | hva
      · have huw : u = w := huniq u hadj.symm
        rcases huw with rfl
        have hnot_aw : ¬ O v u := ((hO.2 u v (hT_le hadj_aw.symm)).mp houv)
        have hlam_v : lam v = lam' u + δ s(v, u) := by simp [lam, val_a, hnot_aw]
        have hlam_u : lam u = lam' u := by simp [lam, haw_ne.symm]
        rw [hlam_v, hlam_u, Sym2.eq_swap]
        ring
      · have hne_edge : s(u, v) ≠ s(a, w) := by
          intro heq
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, _⟩ | ⟨_, rfl⟩
          · exact hua rfl
          · exact hva rfl
        have hadj' : T'.Adj u v := by
          rw [SimpleGraph.deleteEdges_adj]
          exact ⟨hadj, by simpa using hne_edge⟩
        simp [lam, hua, hva, hlam' u v hadj' houv]

lemma trail_split_edge {V : Type} {T : SimpleGraph V} {u v : V}
    (T' : SimpleGraph V) (hT' : ∀ x y, T'.Adj x y → T.Adj x y ∨ s(x, y) = s(u, v)) :
    ∀ {x y : V} (p : T'.Walk x y), p.edges.Nodup →
      (s(u, v) ∉ p.edges → T.Reachable x y) ∧
      (s(u, v) ∈ p.edges → (T.Reachable x u ∧ T.Reachable v y) ∨
        (T.Reachable x v ∧ T.Reachable u y))
  | x, _, .nil, _ => ⟨fun _ => SimpleGraph.Reachable.refl x, fun h => by simp at h⟩
  | x, y, @SimpleGraph.Walk.cons _ _ _ z _ hadj q, hnodup => by
    rw [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
    obtain ⟨hnot_q, hnodup_q⟩ := hnodup
    have ih := trail_split_edge T' hT' q hnodup_q
    constructor
    · intro hnot
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or] at hnot
      rcases hT' x z hadj with hT_xz | heq
      · exact hT_xz.reachable.trans (ih.1 hnot.2)
      · exact False.elim (hnot.1 heq.symm)
    · intro hmem
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hmem
      by_cases heq : s(u, v) = s(x, z)
      · have hnot_in_q : s(u, v) ∉ q.edges := by rwa [heq]
        have hzy : T.Reachable z y := ih.1 hnot_in_q
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · left; exact ⟨SimpleGraph.Reachable.refl _, hzy⟩
        · right; exact ⟨SimpleGraph.Reachable.refl _, hzy⟩
      · have hmem_q : s(u, v) ∈ q.edges := hmem.resolve_left heq
        have hT_xz : T.Adj x z := (hT' x z hadj).resolve_right (Ne.symm heq)
        rcases ih.2 hmem_q with ⟨hzu, hvy⟩ | ⟨hzv, huy⟩
        · left; exact ⟨hT_xz.reachable.trans hzu, hvy⟩
        · right; exact ⟨hT_xz.reachable.trans hzv, huy⟩

lemma exists_spanning_forest {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsAcyclic ∧ ∀ u v, G.Adj u v → T.Reachable u v := by
  let ℱ : Finset (SimpleGraph V) := Finset.univ.filter (fun H => H ≤ G ∧ H.IsAcyclic)
  have hbot : (⊥ : SimpleGraph V) ∈ ℱ := by
    simp only [ℱ, Finset.mem_filter, Finset.mem_univ, true_and, bot_le]
    intro v c hc
    cases c with
    | nil => exact hc.ne_nil rfl
    | cons h _ => exact h
  obtain ⟨T, hT_mem, hT_max⟩ := Finset.exists_max_image ℱ (fun H => (edgesOf H).card) ⟨⊥, hbot⟩
  simp only [ℱ, Finset.mem_filter, Finset.mem_univ, true_and] at hT_mem
  refine ⟨T, hT_mem.1, hT_mem.2, fun u v hadj => ?_⟩
  by_contra hnot_reach
  let T' : SimpleGraph V := T ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
  have hT'_le : T' ≤ G := by
    refine sup_le hT_mem.1 ?_
    intro x y hxy
    rw [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at hxy
    rcases hxy.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm
  have hT'_edge : ∀ x y, T'.Adj x y → T.Adj x y ∨ s(x, y) = s(u, v) := by
    intro x y hxy
    rcases hxy with hT | hE
    · exact Or.inl hT
    · rw [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff] at hE
      exact Or.inr hE.1
  have hT'_acyc : T'.IsAcyclic := by
    intro w c hc
    have hsplit := trail_split_edge (u := u) (v := v) T' hT'_edge c hc.isTrail.edges_nodup
    by_cases hmem : s(u, v) ∈ c.edges
    · apply hnot_reach
      rcases hsplit.2 hmem with ⟨hwu, hvw⟩ | ⟨hwv, huw⟩
      · exact hwu.symm.trans hvw.symm
      · exact huw.trans hwv
    · have h_in_T : ∀ e ∈ c.edges, e ∈ T.edgeSet := by
        intro e he
        have heT' : e ∈ T'.edgeSet := c.edges_subset_edgeSet he
        induction e using Sym2.ind with
        | _ x y =>
          exact (hT'_edge x y heT').resolve_right (fun h => hmem (h ▸ he))
      exact hT_mem.2 (c.transfer T h_in_T) (hc.transfer h_in_T)
  have hT'_mem : T' ∈ ℱ := by
    simp only [ℱ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hT'_le, hT'_acyc⟩
  have hle_card : (edgesOf T').card ≤ (edgesOf T).card := hT_max T' hT'_mem
  have hlt_card : (edgesOf T).card < (edgesOf T').card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro e he
      rw [mem_edgesOf] at he ⊢
      exact SimpleGraph.edgeSet_mono le_sup_left he
    · intro heq
      have huv_in : s(u, v) ∈ edgesOf T' := by
        rw [mem_edgesOf]
        show T'.Adj u v
        right
        rw [SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
        exact ⟨rfl, G.ne_of_adj hadj⟩
      rw [← heq, mem_edgesOf] at huv_in
      exact hnot_reach (SimpleGraph.Adj.reachable huv_in)
  omega

lemma nodup_edges_sum_eq {V : Type} [Fintype V] {G : SimpleGraph V}
    (b : Sym2 V → ℤ) {x : V} {c : G.Walk x x} (hc : c.IsCycle) :
    (c.edges.map fun e => (b e : ZMod 2)).sum =
      ∑ e ∈ edgesOf G, cycleVec c e * (b e : ZMod 2) := by
  have hnodup : c.edges.Nodup := hc.isTrail.edges_nodup
  rw [← List.sum_toFinset _ hnodup]
  have hsub : c.edges.toFinset ⊆ edgesOf G := by
    intro e he
    rw [List.mem_toFinset] at he
    exact mem_edgesOf.mpr (c.edges_subset_edgeSet he)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun e he => ?_
    rw [List.mem_toFinset] at he
    simp [cycleVec, he]
  · intro e _ he_not
    rw [List.mem_toFinset] at he_not
    simp [cycleVec, he_not]

lemma residual_zero_of_cycleBasis {V : Type} [Fintype V]
    (G : SimpleGraph V) (O : V → V → Prop) {k : ℕ} (B : Fin k → CycleOf G)
    (hB : IsCycleBasis B) (T : SimpleGraph V) (hT_le : T ≤ G)
    (hT_reach : ∀ u v, G.Adj u v → T.Reachable u v) :
    ∀ (N : ℕ) (b : Sym2 V → ℤ),
      (∑ e ∈ edgesOf G, (b e).natAbs) ≤ N →
      (∀ i, signedSum O b (B i).walk = 0) →
      (∀ e ∈ T.edgeSet, b e = 0) →
      ∀ e ∈ G.edgeSet, b e = 0 := by
  intro N
  induction N with
  | zero =>
    intro b hsum _ _ e he
    have h0 : ∑ d ∈ edgesOf G, (b d).natAbs = 0 := Nat.eq_zero_of_le_zero hsum
    rw [Finset.sum_eq_zero_iff] at h0
    exact Int.natAbs_eq_zero.mp (h0 e (mem_edgesOf.mpr he))
  | succ N ih =>
    intro b hsum hb_basis hb_T
    by_cases heven : ∀ e ∈ edgesOf G, (2 : ℤ) ∣ b e
    · by_cases hall0 : ∀ e ∈ edgesOf G, b e = 0
      · intro e he; exact hall0 e (mem_edgesOf.mpr he)
      · obtain ⟨e₀, he₀_mem, he₀_ne⟩ := not_forall₂.mp hall0
        let b' : Sym2 V → ℤ := fun e => b e / 2
        have hmul : ∀ e ∈ G.edgeSet, b e = 2 * b' e := by
          intro e he
          exact (Int.mul_ediv_cancel' (heven e (mem_edgesOf.mpr he))).symm
        have hle_each : ∀ e ∈ edgesOf G, (b' e).natAbs ≤ (b e).natAbs := by
          intro e he
          have h := hmul e (mem_edgesOf.mp he)
          omega
        have hlt_e₀ : (b' e₀).natAbs < (b e₀).natAbs := by
          have h := hmul e₀ (mem_edgesOf.mp he₀_mem)
          omega
        have hsum_lt : (∑ e ∈ edgesOf G, (b' e).natAbs) <
            ∑ e ∈ edgesOf G, (b e).natAbs :=
          Finset.sum_lt_sum hle_each ⟨e₀, he₀_mem, hlt_e₀⟩
        have hb'_basis : ∀ i, signedSum O b' (B i).walk = 0 := by
          intro i
          have h2 := signedSum_two_mul O b b' hmul (B i).walk
          rw [hb_basis i] at h2
          omega
        have hb'_T : ∀ e ∈ T.edgeSet, b' e = 0 := by
          intro e he; simp [b', hb_T e he]
        have hb'_zero := ih b' (by omega) hb'_basis hb'_T
        intro e he
        rw [hmul e he, hb'_zero e he, mul_zero]
    · obtain ⟨e₀, he₀_mem, he₀_odd⟩ := not_forall₂.mp heven
      exfalso
      let φ : (Sym2 V → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun f => ∑ e ∈ edgesOf G, f e * (b e : ZMod 2)
          map_add' := fun f g => by simp [add_mul, Finset.sum_add_distrib]
          map_smul' := fun r f => by simp [mul_assoc, Finset.mul_sum] }
      have hker_le : cycleSpace G ≤ LinearMap.ker φ := by
        rw [← hB.2, Submodule.span_le]
        rintro f ⟨i, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        have h1 := signedSum_cast_zmod2 O b (B i).walk
        rw [hb_basis i, Int.cast_zero, nodup_edges_sum_eq b (B i).isCycle] at h1
        exact h1.symm
      have he₀_G : e₀ ∈ G.edgeSet := mem_edgesOf.mp he₀_mem
      induction e₀ using Sym2.ind with
      | _ u₀ v₀ =>
        have hadj_u₀v₀ : G.Adj u₀ v₀ := he₀_G
        have hnot_T : ¬ T.Adj u₀ v₀ := by
          intro hTadj
          have hb0 := hb_T s(u₀, v₀) hTadj
          exact he₀_odd ⟨0, by simp [hb0]⟩
        obtain ⟨p, hp_path⟩ := exists_isPath_of_reachable (hT_reach u₀ v₀ hadj_u₀v₀)
        let pG : G.Walk u₀ v₀ :=
          p.transfer G (fun e he => SimpleGraph.edgeSet_mono hT_le (p.edges_subset_edgeSet he))
        have hpG_path : pG.IsPath := hp_path.transfer _
        have hnot_pG : s(v₀, u₀) ∉ pG.edges := by
          rw [SimpleGraph.Walk.edges_transfer]
          intro hmem
          have hT_mem : s(v₀, u₀) ∈ T.edgeSet := p.edges_subset_edgeSet hmem
          rw [Sym2.eq_swap] at hT_mem
          exact hnot_T hT_mem
        let C₀ : G.Walk v₀ v₀ := SimpleGraph.Walk.cons hadj_u₀v₀.symm pG
        have hC₀_cyc : C₀.IsCycle :=
          (SimpleGraph.Walk.cons_isCycle_iff pG hadj_u₀v₀.symm).mpr ⟨hpG_path, hnot_pG⟩
        have hC₀_ker : cycleVec C₀ ∈ LinearMap.ker φ :=
          hker_le (Submodule.subset_span ⟨v₀, C₀, hC₀_cyc, rfl⟩)
        rw [LinearMap.mem_ker] at hC₀_ker
        have hsum_C₀ : (C₀.edges.map fun e => (b e : ZMod 2)).sum = 0 :=
          (nodup_edges_sum_eq b hC₀_cyc).trans hC₀_ker
        simp only [C₀, pG, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
          SimpleGraph.Walk.edges_transfer] at hsum_C₀
        have hp_zero : (p.edges.map fun e => (b e : ZMod 2)).sum = 0 := by
          apply List.sum_eq_zero
          intro z hz
          rw [List.mem_map] at hz
          obtain ⟨e, he, rfl⟩ := hz
          rw [hb_T e (p.edges_subset_edgeSet he), Int.cast_zero]
        rw [hp_zero, add_zero, Sym2.eq_swap] at hsum_C₀
        exact he₀_odd ((ZMod.intCast_zmod_eq_zero_iff_dvd (b s(u₀, v₀)) 2).mp hsum_C₀)

end Aux33

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (O : V → V → Prop)
    (hO : IsRefOrientation G O) (δ : Sym2 V → ℤ) {k : ℕ} (B : Fin k → CycleOf G)
    (hB : IsCycleBasis B) (h0 : ∀ i, signedSum O δ (B i).walk = 0) :
    (∃ lam : V → ℤ, ∀ u v, O u v → lam v - lam u = δ s(u, v)) ∧
      ∀ (v : V) (W : G.Walk v v), signedSum O δ W = 0 := by
  classical
  obtain ⟨T, hT_le, hT_acyc, hT_reach⟩ := Aux33.exists_spanning_forest G
  obtain ⟨lam, hlam_T⟩ := Aux33.exists_potential_on_acyclic hO δ (Aux33.edgesOf T).card T rfl hT_le hT_acyc
  let δ_lam : Sym2 V → ℤ := fun e =>
    if h : ∃ u v, e = s(u, v) ∧ O u v then
      let u := Classical.choose h
      let v := Classical.choose (Classical.choose_spec h)
      lam v - lam u
    else 0
  have hδ_lam : ∀ u v, O u v → lam v - lam u = δ_lam s(u, v) := by
    intro u v houv
    have hex : ∃ u' v', s(u, v) = s(u', v') ∧ O u' v' := ⟨u, v, rfl, houv⟩
    dsimp only [δ_lam]
    rw [dif_pos hex]
    let u' := Classical.choose hex
    let v' := Classical.choose (Classical.choose_spec hex)
    have hspec : s(u, v) = s(u', v') ∧ O u' v' :=
      Classical.choose_spec (Classical.choose_spec hex)
    obtain ⟨heq, hou'v'⟩ := hspec
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · change lam v - lam u = lam v' - lam u'
      rw [← hu, ← hv]
    · exfalso
      rw [← hu, ← hv] at hou'v'
      exact ((hO.2 u v (hO.1 u v houv)).mp houv) hou'v'
  let b : Sym2 V → ℤ := fun e => δ e - δ_lam e
  have hb_basis : ∀ i, signedSum O b (B i).walk = 0 := by
    intro i
    rw [Aux33.signedSum_sub O δ δ_lam (B i).walk, h0 i,
      Aux33.signedSum_potential hO δ_lam lam hδ_lam (B i).walk, sub_self, sub_zero]
  have hb_T : ∀ e ∈ T.edgeSet, b e = 0 := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadjT : T.Adj u v := he
      have hadjG : G.Adj u v := hT_le hadjT
      by_cases houv : O u v
      · dsimp [b]
        rw [← hδ_lam u v houv, hlam_T u v hadjT houv, sub_self]
      · have hovu : O v u := by
          have := hO.2 u v hadjG
          tauto
        dsimp [b]
        rw [Sym2.eq_swap, ← hδ_lam v u hovu, hlam_T v u hadjT.symm hovu, sub_self]
  have hb_zero := Aux33.residual_zero_of_cycleBasis G O B hB T hT_le hT_reach
    (∑ e ∈ Aux33.edgesOf G, (b e).natAbs) b le_rfl hb_basis hb_T
  have hlam_all : ∀ u v, O u v → lam v - lam u = δ s(u, v) := by
    intro u v houv
    have he : s(u, v) ∈ G.edgeSet := hO.1 u v houv
    have hb0 : δ s(u, v) - δ_lam s(u, v) = 0 := hb_zero s(u, v) he
    rw [hδ_lam u v houv]
    omega
  refine ⟨⟨lam, hlam_all⟩, fun v W => ?_⟩
  rw [Aux33.signedSum_potential hO δ lam hlam_all W, sub_self]
