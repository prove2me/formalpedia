-- Prove2me | solution 1 for Menger27.Graphs.satz_delta
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:04:51.325829+00:00
-- url     : https://prove2.me/submissions/1f98e24c-dc16-4f43-a801-cf32f4d887d4

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts



namespace Menger27.Graphs
theorem sep_of_choice {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q : Finset V) (hPQ : Disjoint P Q) (f : Sym2 V → V) (hf : ∀ e ∈ G.edgeSet, f e ∈ e) :
    Separates G P Q (G.edgeFinset.image f) := by
  intro x hx y hy w
  cases w with
  | nil => exact absurd hy (Finset.disjoint_left.mp hPQ hx)
  | @cons _ v _ h p =>
    have he : s(x, v) ∈ G.edgeFinset := by simpa using h
    have hm := hf s(x, v) (by simpa using h)
    refine ⟨f s(x, v), ?_, Finset.mem_image_of_mem f he⟩
    rcases Sym2.mem_iff.mp hm with h1 | h1
    · rw [h1]; simp
    · rw [h1]; simp

theorem grad_ge_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hG : NPointConnected G P Q n) :
    n ≤ G.edgeFinset.card := by
  classical
  have := hG _ (sep_of_choice G P Q hPQ (fun e : Sym2 V => e.out.1) (fun e _ => Sym2.out_fst_mem e))
  exact this.trans Finset.card_image_le

theorem grad_eq_consists_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hG : NPointConnected G P Q n) (hgrad : G.edgeFinset.card = n) :
    ∃ (a b : Fin n → V) (w : ∀ i, G.Walk (a i) (b i)),
      (∀ i, a i ∈ P ∧ b i ∈ Q ∧ (w i).IsPath) ∧
      (∀ i j, i ≠ j → List.Disjoint (w i).support (w j).support) ∧
      ∀ e ∈ G.edgeSet, ∃ i, e ∈ (w i).edges := by
  classical
  -- injectivity of any choice function
  have hinj : ∀ f : Sym2 V → V, (∀ e ∈ G.edgeSet, f e ∈ e) → Set.InjOn f (G.edgeFinset : Set (Sym2 V)) := by
    intro f hf
    have h1 := hG _ (sep_of_choice G P Q hPQ f hf)
    have h2 : (G.edgeFinset.image f).card = G.edgeFinset.card := le_antisymm Finset.card_image_le (hgrad ▸ h1)
    exact Finset.card_image_iff.mp h2
  -- matching
  have hmatch : ∀ e1 ∈ G.edgeFinset, ∀ e2 ∈ G.edgeFinset, ∀ v, v ∈ e1 → v ∈ e2 → e1 = e2 := by
    intro e1 h1 e2 h2 v hv1 hv2
    by_contra hne
    let f : Sym2 V → V := fun e => if e = e1 ∨ e = e2 then v else e.out.1
    have hf : ∀ e ∈ G.edgeSet, f e ∈ e := by
      intro e _
      by_cases hc : e = e1 ∨ e = e2
      · simp only [f, if_pos hc]; rcases hc with rfl | rfl <;> assumption
      · simp only [f, if_neg hc]; exact Sym2.out_fst_mem e
    have := hinj f hf h1 h2 (by simp [f, hne])
    exact hne this
  -- every edge joins P and Q
  have hPQe : ∀ e ∈ G.edgeFinset, ∃ x y, e = s(x, y) ∧ x ∈ P ∧ y ∈ Q := by
    intro e he
    let f : Sym2 V → V := fun e => e.out.1
    have hf : ∀ e ∈ G.edgeSet, f e ∈ e := fun e _ => Sym2.out_fst_mem e
    have hS := sep_of_choice G P Q hPQ f hf
    have hcard : (G.edgeFinset.image f).card = n := le_antisymm (Finset.card_image_le.trans hgrad.le) (hG _ hS)
    have hns : ¬ Separates G P Q ((G.edgeFinset.image f).erase (f e)) := by
      intro h
      have := hG _ h
      rw [Finset.card_erase_of_mem (Finset.mem_image_of_mem f he), hcard] at this
      have : 0 < n := by rw [← hcard]; exact Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem f he⟩
      omega
    unfold Separates at hns
    push_neg at hns
    obtain ⟨x, hx, y, hy, w, hw⟩ := hns
    -- first edge of any such walk is e
    have key : ∀ {x y : V} (w : G.Walk x y), x ≠ y →
        (∀ v ∈ w.support, v ∉ (G.edgeFinset.image f).erase (f e)) → ∃ v, e = s(x, v) := by
      intro x y w hxy hw
      cases w with
      | nil => exact absurd rfl hxy
      | @cons _ v _ h p =>
        have he' : s(x, v) ∈ G.edgeFinset := by simpa using h
        have hm := hf s(x, v) (by simpa using h)
        have hsup : f s(x, v) ∈ (SimpleGraph.Walk.cons h p).support := by
          rcases Sym2.mem_iff.mp hm with h1 | h1
          · rw [h1]; simp
          · rw [h1]; simp
        have := hw _ hsup
        have hmem : f s(x, v) ∈ G.edgeFinset.image f := Finset.mem_image_of_mem f he'
        have heq : f s(x, v) = f e := by
          by_contra hne; exact this (Finset.mem_erase.mpr ⟨hne, hmem⟩)
        exact ⟨v, (hinj f hf he he' heq.symm)⟩
    have hxy : x ≠ y := fun h => Finset.disjoint_left.mp hPQ hx (h ▸ hy)
    obtain ⟨v, hv⟩ := key w hxy hw
    obtain ⟨v', hv'⟩ := key w.reverse hxy.symm (by simpa using hw)
    have hye : y ∈ e := by rw [hv']; simp
    rw [hv] at hye
    rcases Sym2.mem_iff.mp hye with h | h
    · exact absurd h.symm hxy
    · exact ⟨x, y, by rw [hv, h], hx, hy⟩
  let ε : Fin n ≃ G.edgeFinset := (Finset.equivFinOfCardEq hgrad).symm
  have hc : ∀ i, ∃ x y, (ε i : Sym2 V) = s(x, y) ∧ x ∈ P ∧ y ∈ Q := fun i => hPQe _ (ε i).2
  choose a b hab haP hbQ using hc
  have hadj : ∀ i, G.Adj (a i) (b i) := by
    intro i
    have := (ε i).2
    rw [hab i] at this
    simpa using this
  refine ⟨a, b, fun i => (hadj i).toWalk, ?_, ?_, ?_⟩
  · intro i
    refine ⟨haP i, hbQ i, ?_⟩
    simp [SimpleGraph.Walk.isPath_def, (hadj i).ne]
  · intro i j hij v hv1 hv2
    simp at hv1 hv2
    have h1 : v ∈ (ε i : Sym2 V) := by rw [hab i]; rcases hv1 with rfl | rfl <;> simp
    have h2 : v ∈ (ε j : Sym2 V) := by rw [hab j]; rcases hv2 with rfl | rfl <;> simp
    exact hij (ε.injective (Subtype.ext (hmatch _ (ε i).2 _ (ε j).2 v h1 h2)))
  · intro e he
    have he' : e ∈ G.edgeFinset := by simpa using he
    obtain ⟨i, hi⟩ := ε.surjective ⟨e, he'⟩
    refine ⟨i, ?_⟩
    have : e = s(a i, b i) := by rw [← hab i, hi]
    simp [this]

theorem exists_irreducible_part_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n) :
    ∃ K : SimpleGraph V, K ≤ G ∧ IrreduciblyNPointConnected K P Q n := by
  classical
  let S : Set (SimpleGraph V) := {K | K ≤ G ∧ NPointConnected K P Q n}
  obtain ⟨K, hK, hmin⟩ := WellFounded.has_min wellFounded_lt S ⟨G, le_rfl, hG⟩
  refine ⟨K, hK.1, hK.2, fun H hH hH' => hmin H ⟨hH.le.trans hK.1, hH'⟩ hH⟩

theorem exists_separator_through_core {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hK : IrreduciblyNPointConnected K P Q n) (hgrad : n < K.edgeFinset.card)
    (s : V) (hsP : s ∉ P) (hsQ : s ∉ Q) (t : V) (hst : K.Adj s t) :
    ∃ S : Finset V, s ∈ S ∧ S.card = n ∧ Separates K P Q S := by
  classical
  have hlt : K.deleteEdges {s(s, t)} < K := by
    refine lt_of_le_of_ne (SimpleGraph.deleteEdges_le _) ?_
    intro h
    have h2 : (K.deleteEdges {s(s, t)}).Adj s t := by rw [h]; exact hst
    simp [SimpleGraph.deleteEdges_adj] at h2
  obtain ⟨T, hT, hTc⟩ : ∃ T, Separates (K.deleteEdges {s(s, t)}) P Q T ∧ T.card < n := by
    have := hK.2 _ hlt
    unfold NPointConnected at this
    push_neg at this
    exact this
  have hsep : Separates K P Q (insert s T) := by
    intro x hx y hy w
    by_cases hs : s ∈ w.support
    · exact ⟨s, hs, Finset.mem_insert_self _ _⟩
    · have hw : ∀ e ∈ w.edges, e ∉ ({s(s, t)} : Set (Sym2 V)) := by
        intro e he hmem
        have : e = s(s, t) := hmem
        subst this
        exact hs (w.fst_mem_support_of_mem_edges he)
      have hE : ∀ e ∈ w.edges, e ∈ (K.deleteEdges {s(s, t)}).edgeSet := by
        intro e he
        rw [SimpleGraph.edgeSet_deleteEdges]
        exact ⟨w.edges_subset_edgeSet he, hw e he⟩
      obtain ⟨v, hv, hvT⟩ := hT x hx y hy (w.transfer _ hE)
      rw [SimpleGraph.Walk.support_transfer] at hv
      exact ⟨v, hv, Finset.mem_insert_of_mem hvT⟩
  have hc := hK.1 _ hsep
  have hc2 : (insert s T).card ≤ n := (Finset.card_insert_le _ _).trans (by omega)
  exact ⟨insert s T, Finset.mem_insert_self _ _, le_antisymm hc2 hc, hsep⟩

theorem sideVerts_not_mem {V : Type*} (G : SimpleGraph V) (P S : Finset V) {u : V}
    (hu : u ∈ sideVerts G P S) : u ∉ S := by
  obtain ⟨x, hx, w, hw⟩ := hu
  exact hw u w.end_mem_support

theorem sideVerts_of_P {V : Type*} (G : SimpleGraph V) (P S : Finset V) {x : V}
    (hx : x ∈ P) (hxS : x ∉ S) : x ∈ sideVerts G P S :=
  ⟨x, hx, SimpleGraph.Walk.nil, by simpa using hxS⟩

theorem first_hit {V : Type*} (G : SimpleGraph V) (P S : Finset V) {u y : V} (w : G.Walk u y) :
    u ∈ sideVerts G P S → (∃ v ∈ w.support, v ∈ S) →
    (∃ v ∈ w.support, v ∈ S ∧ v ∈ P) ∨
      ∃ v ∈ S, v ∉ P ∧ ∃ w' : (sidePart G P S).Walk u v, ∀ z ∈ w'.support, z ∈ w.support := by
  induction w with
  | nil =>
    intro hu ⟨v, hv, hvS⟩
    simp at hv
    subst hv
    exact absurd hvS (sideVerts_not_mem G P S hu)
  | @cons u z y h p ih =>
    intro hu ⟨v, hv, hvS⟩
    by_cases hz : z ∈ S
    · by_cases hzP : z ∈ P
      · exact Or.inl ⟨z, by simp, hz, hzP⟩
      · refine Or.inr ⟨z, hz, hzP, (show (sidePart G P S).Adj u z from
          ⟨h, Or.inl hu, Or.inl hu, Or.inr ⟨hz, hzP⟩⟩).toWalk, ?_⟩
        intro q hq
        simp at hq
        rcases hq with rfl | rfl <;> simp
    · have hzsv : z ∈ sideVerts G P S := by
        obtain ⟨x, hx, wx, hwx⟩ := hu
        refine ⟨x, hx, wx.concat h, ?_⟩
        intro q hq
        rw [SimpleGraph.Walk.support_concat] at hq
        simp at hq
        rcases hq with hq | rfl
        · exact hwx q hq
        · exact hz
      have hv' : ∃ v ∈ p.support, v ∈ S := by
        simp at hv
        rcases hv with rfl | hv
        · exact absurd hvS (sideVerts_not_mem G P S hu)
        · exact ⟨v, hv, hvS⟩
      rcases ih hzsv hv' with ⟨q, hq, hqS, hqP⟩ | ⟨q, hqS, hqP, w', hw'⟩
      · exact Or.inl ⟨q, by simp [hq], hqS, hqP⟩
      · refine Or.inr ⟨q, hqS, hqP, SimpleGraph.Walk.cons
          (show (sidePart G P S).Adj u z from ⟨h, Or.inl hu, Or.inl hu, Or.inl hzsv⟩) w', ?_⟩
        intro r hr
        simp at hr
        rcases hr with rfl | hr
        · simp
        · simp [hw' r hr]

theorem side_npoint_connected_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n)
    (S : Finset V) (hS : Separates G P Q S) (hcard : S.card = n) :
    NPointConnected (sidePart G P S) (P \ S) (S \ P) (n - (S ∩ P).card) := by
  intro T hT
  have hsep : Separates G P Q (T ∪ (S ∩ P)) := by
    intro x hx y hy w
    by_cases hxS : x ∈ S
    · exact ⟨x, w.start_mem_support, Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxS, hx⟩)⟩
    · obtain ⟨v, hv, hvS⟩ := hS x hx y hy w
      rcases first_hit G P S w (sideVerts_of_P G P S hx hxS) ⟨v, hv, hvS⟩ with
        ⟨q, hq, hqS, hqP⟩ | ⟨q, hqS, hqP, w', hw'⟩
      · exact ⟨q, hq, Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hqS, hqP⟩)⟩
      · obtain ⟨z, hz, hzT⟩ := hT x (Finset.mem_sdiff.mpr ⟨hx, hxS⟩) q
          (Finset.mem_sdiff.mpr ⟨hqS, hqP⟩) w'
        exact ⟨z, hw' z hz, Finset.mem_union_left _ hzT⟩
  have h1 := hG _ hsep
  have h2 := Finset.card_union_le T (S ∩ P)
  omega

theorem pq_step {V : Type*} (K : SimpleGraph V) (P Q : Finset V) (hPQ : Disjoint P Q)
    (hyp : ∀ s : V, s ∉ P → s ∉ Q → ∀ t : V, ¬ K.Adj s t) {a b : V} (w : K.Walk a b)
    (ha : a ∈ P) (hb : b ∈ Q) : ∃ u v, K.Adj u v ∧ u ∈ P ∧ v ∈ Q ∧ u ∈ w.support ∧ v ∈ w.support := by
  induction w with
  | nil => exact absurd hb (Finset.disjoint_left.mp hPQ ha)
  | @cons a z b h p ih =>
    by_cases hz : z ∈ Q
    · exact ⟨a, z, h, ha, hz, by simp, by simp⟩
    · have hzP : z ∈ P := by
        by_contra hzP
        exact hyp z hzP hz a h.symm
      obtain ⟨u, v, huv, hu, hv, hus, hvs⟩ := ih hzP hb
      exact ⟨u, v, huv, hu, hv, by simp [hus], by simp [hvs]⟩

theorem cover_sep {V : Type*} (K : SimpleGraph V) (P Q : Finset V) (hPQ : Disjoint P Q)
    (hyp : ∀ s : V, s ∉ P → s ∉ Q → ∀ t : V, ¬ K.Adj s t) (T : Finset V)
    (hT : ∀ u ∈ P, ∀ v ∈ Q, K.Adj u v → u ∈ T ∨ v ∈ T) : Separates K P Q T := by
  intro x hx y hy w
  obtain ⟨u, v, huv, hu, hv, hus, hvs⟩ := pq_step K P Q hPQ hyp w hx hy
  rcases hT u hu v hv huv with h | h
  · exact ⟨u, hus, h⟩
  · exact ⟨v, hvs, h⟩

theorem exists_vertex_not_mem_core {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hK : IrreduciblyNPointConnected K P Q n) (hgrad : n < K.edgeFinset.card) :
    ∃ s : V, s ∉ P ∧ s ∉ Q ∧ ∃ t : V, K.Adj s t := by
  classical
  by_contra hcon
  have hyp : ∀ s : V, s ∉ P → s ∉ Q → ∀ t : V, ¬ K.Adj s t := by
    intro s h1 h2 t h3
    exact hcon ⟨s, h1, h2, t, h3⟩
  have hcov : ∀ T : Finset V, (∀ u ∈ P, ∀ v ∈ Q, K.Adj u v → u ∈ T ∨ v ∈ T) → n ≤ T.card :=
    fun T hT => hK.1 T (cover_sep K P Q hPQ hyp T hT)
  have hnP : n ≤ P.card := hcov P (fun u hu v hv _ => Or.inl hu)
  obtain ⟨d, hd⟩ : ∃ d, P.card = n + d := ⟨P.card - n, by omega⟩
  let t : P → Finset (V ⊕ Fin d) := fun x =>
    (Q.filter (K.Adj x.1)).image Sum.inl ∪ (Finset.univ : Finset (Fin d)).image Sum.inr
  have hall : ∀ X : Finset P, X.card ≤ (X.biUnion t).card := by
    intro X
    rcases X.eq_empty_or_nonempty with rfl | hXne
    · simp
    set N : Finset V := Q.filter (fun v => ∃ x ∈ X, K.Adj x.1 v) with hN
    have hsub : N.image Sum.inl ∪ (Finset.univ : Finset (Fin d)).image Sum.inr ⊆ X.biUnion t := by
      intro z hz
      rw [Finset.mem_union] at hz
      rw [Finset.mem_biUnion]
      rcases hz with hz | hz
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨hvQ, x, hx, hxv⟩ := Finset.mem_filter.mp hv
        exact ⟨x, hx, Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨v, Finset.mem_filter.mpr ⟨hvQ, hxv⟩, rfl⟩)⟩
      · obtain ⟨x, hx⟩ := hXne
        exact ⟨x, hx, Finset.mem_union_right _ hz⟩
    have hdisj : Disjoint (N.image (Sum.inl : V → V ⊕ Fin d)) ((Finset.univ : Finset (Fin d)).image Sum.inr) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨i, _, h⟩ := Finset.mem_image.mp hz'
      cases h
    have hcard1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective] at hcard1
    simp only [Finset.card_univ, Fintype.card_fin] at hcard1
    -- cover
    set Xm : Finset V := X.map (Function.Embedding.subtype _) with hXm
    have hXmP : Xm ⊆ P := by
      intro z hz
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hz
      exact x.2
    have hT := hcov (N ∪ (P \ Xm)) (by
      intro u hu v hv huv
      by_cases hux : (⟨u, hu⟩ : P) ∈ X
      · right
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, ⟨u, hu⟩, hux, huv⟩)
      · left
        refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hu, ?_⟩)
        intro hm
        obtain ⟨x, hx, hxu⟩ := Finset.mem_map.mp hm
        apply hux
        have : x = ⟨u, hu⟩ := Subtype.ext hxu
        rwa [← this])
    have h1 := Finset.card_union_le N (P \ Xm)
    have h2 := Finset.card_sdiff_add_card_eq_card hXmP
    have h3 : Xm.card = X.card := by simp [hXm]
    omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  let A : Finset P := Finset.univ.filter (fun x => ∃ y, f x = Sum.inl y)
  let B : Finset P := Finset.univ.filter (fun x => ∃ i, f x = Sum.inr i)
  have hAB : (Finset.univ : Finset P) ⊆ A ∪ B := by
    intro x _
    rcases h : f x with y | i
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, h⟩)
  have hB : B.card ≤ d := by
    have : B.image f ⊆ (Finset.univ : Finset (Fin d)).image Sum.inr := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨_, i, hi⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.symm⟩
    have h2 := Finset.card_le_card this
    rwa [Finset.card_image_of_injective _ hfinj, Finset.card_image_of_injective _ Sum.inr_injective,
      Finset.card_univ, Fintype.card_fin] at h2
  have hA : n ≤ A.card := by
    have h1 := Finset.card_le_card hAB
    have h2 := Finset.card_union_le A B
    simp only [Finset.card_univ, Fintype.card_coe] at h1
    omega
  obtain ⟨A', hA'A, hA'c⟩ := Finset.exists_subset_card_eq hA
  let g : P → V := fun x => if h : ∃ y, f x = Sum.inl y then h.choose else x.1
  have hg : ∀ x ∈ A, f x = Sum.inl (g x) := by
    intro x hx
    obtain ⟨_, h⟩ := Finset.mem_filter.mp hx
    simp only [g, dif_pos h]
    exact h.choose_spec
  have hgQ : ∀ x ∈ A, g x ∈ Q ∧ K.Adj x.1 (g x) := by
    intro x hx
    have h1 := hft x
    rw [hg x hx] at h1
    simp only [t, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at h1
    rcases h1 with ⟨v, ⟨hvQ, hva⟩, hv⟩ | ⟨i, _, hi⟩
    · cases hv; exact ⟨hvQ, hva⟩
    · cases hi
  let M' : Finset (Sym2 V) := A'.image (fun x => s(x.1, g x))
  have hM'c : M'.card ≤ n := hA'c ▸ Finset.card_image_le
  obtain ⟨e, heE, heM⟩ := Finset.exists_mem_notMem_of_card_lt_card (lt_of_le_of_lt hM'c hgrad)
  have hlt : K.deleteEdges {e} < K := by
    refine lt_of_le_of_ne (SimpleGraph.deleteEdges_le _) ?_
    intro h
    induction e using Sym2.ind with
    | _ a b =>
      have hab : K.Adj a b := by simpa using heE
      have h2 : (K.deleteEdges {s(a, b)}).Adj a b := by rw [h]; exact hab
      simp [SimpleGraph.deleteEdges_adj] at h2
  apply hK.2 _ hlt
  intro T hT
  let φ : P → V := fun x => if x.1 ∈ T then x.1 else g x
  have hmap : ∀ x ∈ A', φ x ∈ T := by
    intro x hx
    by_cases hxT : x.1 ∈ T
    · simp [φ, hxT]
    · simp only [φ, if_neg hxT]
      have hxA := hA'A hx
      obtain ⟨hgq, hga⟩ := hgQ x hxA
      have hadj : (K.deleteEdges {e}).Adj x.1 (g x) := by
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨hga, ?_⟩
        intro hm
        apply heM
        have : e = s(x.1, g x) := (Set.mem_singleton_iff.mp hm).symm
        rw [this]
        exact Finset.mem_image_of_mem _ hx
      obtain ⟨z, hz, hzT⟩ := hT x.1 x.2 (g x) hgq hadj.toWalk
      simp at hz
      rcases hz with rfl | rfl
      · exact absurd hzT hxT
      · exact hzT
  have hinj : Set.InjOn φ (A' : Set P) := by
    intro x hx y hy hxy
    have hxA := hA'A hx
    have hyA := hA'A hy
    obtain ⟨hgx, _⟩ := hgQ x hxA
    obtain ⟨hgy, _⟩ := hgQ y hyA
    by_cases hxT : x.1 ∈ T <;> by_cases hyT : y.1 ∈ T
    · simp only [φ, if_pos hxT, if_pos hyT] at hxy; exact Subtype.ext hxy
    · simp only [φ, if_pos hxT, if_neg hyT] at hxy
      exact absurd (by rw [hxy]; exact hgy : x.1 ∈ Q) (Finset.disjoint_left.mp hPQ x.2)
    · simp only [φ, if_neg hxT, if_pos hyT] at hxy
      exact absurd (by rw [← hxy]; exact hgx : y.1 ∈ Q) (Finset.disjoint_left.mp hPQ y.2)
    · simp only [φ, if_neg hxT, if_neg hyT] at hxy
      have h : f x = f y := by rw [hg x hxA, hg y hyA, hxy]
      exact hfinj h
  have := Finset.card_le_card_of_injOn φ (fun x hx => hmap x hx) hinj
  omega

theorem sidePart_le {V : Type*} (G : SimpleGraph V) (P S : Finset V) : sidePart G P S ≤ G :=
  fun _ _ h => h.1

theorem sideVerts_extend {V : Type*} (G : SimpleGraph V) (P S : Finset V) {a c : V}
    (ha : a ∈ sideVerts G P S) (h : G.Adj a c) (hc : c ∉ S) : c ∈ sideVerts G P S := by
  obtain ⟨x, hx, wx, hwx⟩ := ha
  refine ⟨x, hx, wx.concat h, ?_⟩
  intro q hq
  rw [SimpleGraph.Walk.support_concat] at hq
  simp at hq
  rcases hq with hq | rfl
  · exact hwx q hq
  · exact hc

theorem sidePart_walk_S {V : Type*} (G : SimpleGraph V) (P S : Finset V) {a b : V}
    (w : (sidePart G P S).Walk a b) (ha : a ∈ S → a ∉ P) :
    ∀ z ∈ w.support, z ∈ S → z ∉ P := by
  induction w with
  | nil => intro z hz; simp at hz; subst hz; exact ha
  | @cons a c b h p ih =>
    intro z hz
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ha
    · apply ih _ z hz
      intro hcS
      have h' : G.Adj a c ∧ (a ∈ sideVerts G P S ∨ c ∈ sideVerts G P S) ∧
        (a ∈ sideVerts G P S ∨ (a ∈ S ∧ a ∉ P)) ∧ (c ∈ sideVerts G P S ∨ (c ∈ S ∧ c ∉ P)) := h
      rcases h'.2.2.2 with h4 | ⟨_, h4⟩
      · exact absurd hcS (sideVerts_not_mem G P S h4)
      · exact h4

theorem sidePart_walk_sv {V : Type*} (G : SimpleGraph V) (P S : Finset V) {a b : V}
    (w : (sidePart G P S).Walk a b) (hw : w.IsPath)
    (ha : a ∈ sideVerts G P S) (hS : ∀ y ∈ w.support, y ∈ S → y = b) :
    ∀ z ∈ w.support, z = b ∨ z ∈ sideVerts G P S := by
  induction w with
  | nil => intro z hz; simp at hz; exact Or.inl hz
  | @cons a c b h p ih =>
    intro z hz
    rw [SimpleGraph.Walk.cons_isPath_iff] at hw
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Or.inr ha
    · by_cases hcS : c ∈ S
      · have hcb : c = b := hS c (by simp) hcS
        subst hcb
        have := SimpleGraph.Walk.isPath_iff_eq_nil.mp hw.1
        subst this
        simp at hz
        exact Or.inl hz
      · have hcsv : c ∈ sideVerts G P S := sideVerts_extend G P S ha h.1 hcS
        exact ih hw.1 hcsv (fun y hy hyS => hS y (by simp [hy]) hyS) z hz

theorem side_family {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (P S : Finset V)
    (hP : HasDisjointPaths (sidePart G P S) (P \ S) (S \ P) (S \ P).card) :
    ∃ (α : S → V) (p : ∀ s : S, G.Walk (α s) s.1),
      (∀ s, α s ∈ P) ∧ (∀ s, (p s).IsPath) ∧
      (∀ s s' : S, s ≠ s' → List.Disjoint (p s).support (p s').support) ∧
      (∀ s, ∀ z ∈ (p s).support, z = s.1 ∨ z ∈ sideVerts G P S) := by
  classical
  obtain ⟨a, b, w, hw, hdisj⟩ := hP
  have hb : ∀ i, b i ∈ S \ P := fun i => (hw i).2.1
  have hbinj : Function.Injective b := by
    intro i j hij
    by_contra hne
    have h2 : b i ∈ (w j).support := by rw [hij]; exact (w j).end_mem_support
    exact hdisj i j hne (w i).end_mem_support h2
  have hbsurj : ∀ y ∈ S \ P, ∃ i, b i = y := by
    have hsub : (Finset.univ : Finset (Fin (S \ P).card)).image b ⊆ S \ P := by
      intro y hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact hb i
    have hc : (S \ P).card ≤ ((Finset.univ : Finset (Fin (S \ P).card)).image b).card := by
      rw [Finset.card_image_of_injective _ hbinj]; simp
    have heq := Finset.eq_of_subset_of_card_le hsub hc
    intro y hy
    rw [← heq] at hy
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hy
    exact ⟨i, hi⟩
  have hwS : ∀ i, ∀ y ∈ (w i).support, y ∈ S → y = b i := by
    intro i y hy hyS
    have hy' : y ∉ P := sidePart_walk_S G P S (w i)
      (fun h => absurd h (Finset.mem_sdiff.mp (hw i).1).2) y hy hyS
    obtain ⟨j, hj⟩ := hbsurj y (Finset.mem_sdiff.mpr ⟨hyS, hy'⟩)
    by_cases hij : i = j
    · rw [← hj, hij]
    · have hyj : y ∈ (w j).support := by rw [← hj]; exact (w j).end_mem_support
      exact absurd hyj (fun h => hdisj i j hij hy h)
  have hwsv : ∀ i, ∀ z ∈ (w i).support, z = b i ∨ z ∈ sideVerts G P S := fun i =>
    sidePart_walk_sv G P S (w i) (hw i).2.2
      (sideVerts_of_P G P S (Finset.mem_sdiff.mp (hw i).1).1 (Finset.mem_sdiff.mp (hw i).1).2)
      (hwS i)
  have claim : ∀ s : S, ∃ (α : V) (p : G.Walk α s.1), α ∈ P ∧ p.IsPath ∧
      (∀ z ∈ p.support, z = s.1 ∨ z ∈ sideVerts G P S) ∧ (s.1 ∈ P → p.support = [s.1]) ∧
      (s.1 ∉ P → ∃ i, b i = s.1 ∧ p.support = (w i).support) := by
    intro s
    by_cases hsP : s.1 ∈ P
    · exact ⟨s.1, SimpleGraph.Walk.nil, hsP, by simp,
        by intro z hz; simp at hz; exact Or.inl hz, fun _ => by simp, fun h => absurd hsP h⟩
    · obtain ⟨i, hi⟩ := hbsurj s.1 (Finset.mem_sdiff.mpr ⟨s.2, hsP⟩)
      refine ⟨a i, ((w i).mapLe (sidePart_le G P S)).copy rfl hi,
        (Finset.mem_sdiff.mp (hw i).1).1, ?_, ?_, fun h => absurd h hsP, ?_⟩
      · rw [SimpleGraph.Walk.isPath_copy]
        exact (SimpleGraph.Walk.isPath_mapLe _).mpr (hw i).2.2
      · intro z hz
        rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_mapLe_eq_support] at hz
        rcases hwsv i z hz with h | h
        · exact Or.inl (h.trans hi)
        · exact Or.inr h
      · intro _
        exact ⟨i, hi, by rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_mapLe_eq_support]⟩
  choose α p hα hpath hsv hP1 hP2 using claim
  refine ⟨α, p, hα, hpath, ?_, hsv⟩
  intro s s' hss' z hz hz'
  by_cases hs : s.1 ∈ P <;> by_cases hs' : s'.1 ∈ P
  · rw [hP1 s hs] at hz; rw [hP1 s' hs'] at hz'
    simp at hz hz'
    exact hss' (Subtype.ext (hz.symm.trans hz'))
  · rw [hP1 s hs] at hz
    simp at hz
    rcases hsv s' z hz' with h | h
    · exact hss' (Subtype.ext (hz.symm.trans h))
    · exact sideVerts_not_mem G P S h (by rw [hz]; exact s.2)
  · rw [hP1 s' hs'] at hz'
    simp at hz'
    rcases hsv s z hz with h | h
    · exact hss' (Subtype.ext (h.symm.trans hz'))
    · exact sideVerts_not_mem G P S h (by rw [hz']; exact s'.2)
  · obtain ⟨i, hi, hsup⟩ := hP2 s hs
    obtain ⟨j, hj, hsup'⟩ := hP2 s' hs'
    have hne : i ≠ j := by
      intro h; subst h
      exact hss' (Subtype.ext (hi.symm.trans hj))
    rw [hsup] at hz; rw [hsup'] at hz'
    exact hdisj i j hne hz hz'

theorem sideVerts_disjoint {V : Type*} (G : SimpleGraph V) (P Q S : Finset V)
    (hS : Separates G P Q S) {z : V} (h1 : z ∈ sideVerts G P S) (h2 : z ∈ sideVerts G Q S) :
    False := by
  obtain ⟨x, hx, wx, hwx⟩ := h1
  obtain ⟨y, hy, wy, hwy⟩ := h2
  obtain ⟨v, hv, hvS⟩ := hS x hx y hy (wx.append wy.reverse)
  rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse] at hv
  rcases List.mem_append.mp hv with h | h
  · exact hwx v h hvS
  · exact hwy v (by
      have := List.mem_of_mem_tail h
      simpa using this) hvS

theorem glue_paths_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (S : Finset V) (hS : Separates G P Q S) (hcard : S.card = n)
    (hP : HasDisjointPaths (sidePart G P S) (P \ S) (S \ P) (n - (S ∩ P).card))
    (hQ : HasDisjointPaths (sidePart G Q S) (Q \ S) (S \ Q) (n - (S ∩ Q).card)) :
    HasDisjointPaths G P Q n := by
  classical
  have hP' : HasDisjointPaths (sidePart G P S) (P \ S) (S \ P) (S \ P).card := by
    have h1 := Finset.card_sdiff_add_card_inter S P
    have : n - (S ∩ P).card = (S \ P).card := by omega
    rwa [this] at hP
  have hQ' : HasDisjointPaths (sidePart G Q S) (Q \ S) (S \ Q) (S \ Q).card := by
    have h1 := Finset.card_sdiff_add_card_inter S Q
    have : n - (S ∩ Q).card = (S \ Q).card := by omega
    rwa [this] at hQ
  obtain ⟨α, p, hα, hp, hpd, hpsv⟩ := side_family G P S hP'
  obtain ⟨β, q, hβ, hq, hqd, hqsv⟩ := side_family G Q S hQ'
  let e : S ≃ Fin n := Finset.equivFinOfCardEq hcard
  refine ⟨fun i => α (e.symm i), fun i => β (e.symm i),
    fun i => (p (e.symm i)).append (q (e.symm i)).reverse, ?_, ?_⟩
  · intro i
    refine ⟨hα _, hβ _, ?_⟩
    set s := e.symm i
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append, List.nodup_append]
    have hr : (q s).reverse.support.Nodup := ((hq s).reverse).support_nodup
    refine ⟨(hp s).support_nodup, hr.sublist (List.tail_sublist _), ?_⟩
    intro z hz z' hz' hzz
    subst hzz
    have hzr : z ∈ (q s).support := by
      have := List.mem_of_mem_tail hz'
      simpa [SimpleGraph.Walk.support_reverse] using this
    have htail : s.1 ∉ (q s).reverse.support.tail := by
      have := (SimpleGraph.Walk.cons_tail_support (q s).reverse) ▸ hr
      exact (List.nodup_cons.mp this).1
    rcases hpsv s z hz with h1 | h1 <;> rcases hqsv s z hzr with h2 | h2
    · exact htail (h1 ▸ hz')
    · exact sideVerts_not_mem G Q S h2 (h1 ▸ s.2)
    · exact sideVerts_not_mem G P S h1 (h2 ▸ s.2)
    · exact sideVerts_disjoint G P Q S hS h1 h2
  · intro i j hij z hz hz'
    have hne : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    set s := e.symm i
    set s' := e.symm j
    simp only [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse] at hz hz'
    have hz1 : z ∈ (p s).support ∨ z ∈ (q s).support := by
      rcases List.mem_append.mp hz with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa using List.mem_of_mem_tail h)
    have hz2 : z ∈ (p s').support ∨ z ∈ (q s').support := by
      rcases List.mem_append.mp hz' with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa using List.mem_of_mem_tail h)
    rcases hz1 with h1 | h1 <;> rcases hz2 with h2 | h2
    · exact hpd s s' hne h1 h2
    · rcases hpsv s z h1 with a1 | a1 <;> rcases hqsv s' z h2 with a2 | a2
      · exact hne (Subtype.ext (a1.symm.trans a2))
      · exact sideVerts_not_mem G Q S a2 (a1 ▸ s.2)
      · exact sideVerts_not_mem G P S a1 (a2 ▸ s'.2)
      · exact sideVerts_disjoint G P Q S hS a1 a2
    · rcases hqsv s z h1 with a1 | a1 <;> rcases hpsv s' z h2 with a2 | a2
      · exact hne (Subtype.ext (a1.symm.trans a2))
      · exact sideVerts_not_mem G P S a2 (a1 ▸ s.2)
      · exact sideVerts_not_mem G Q S a1 (a2 ▸ s'.2)
      · exact sideVerts_disjoint G P Q S hS a2 a1
    · exact hqd s s' hne h1 h2

theorem sep_symm {V : Type*} (G : SimpleGraph V) {P Q S : Finset V} (h : Separates G P Q S) :
    Separates G Q P S := by
  intro x hx y hy w
  obtain ⟨v, hv, hvS⟩ := h y hy x hx w.reverse
  exact ⟨v, by simpa using hv, hvS⟩

theorem npc_symm {V : Type*} (G : SimpleGraph V) {P Q : Finset V} {n : ℕ}
    (h : NPointConnected G P Q n) : NPointConnected G Q P n :=
  fun S hS => h S (sep_symm G hS)

theorem lift_paths {V : Type*} {K G : SimpleGraph V} (hle : K ≤ G) {P Q : Finset V} {n : ℕ}
    (h : HasDisjointPaths K P Q n) : HasDisjointPaths G P Q n := by
  obtain ⟨a, b, w, h1, h2⟩ := h
  refine ⟨a, b, fun i => (w i).mapLe hle, fun i => ⟨(h1 i).1, (h1 i).2.1, ?_⟩, ?_⟩
  · exact (SimpleGraph.Walk.isPath_mapLe _).mpr (h1 i).2.2
  · intro i j hij
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using h2 i j hij

theorem nbr_walk {V : Type*} (K : SimpleGraph V) (P S : Finset V) {a b : V} (w : K.Walk a b)
    (ha : a ∈ sideVerts K P S) (hab : a ≠ b) (hS : ∀ y ∈ w.support, y ∈ S → y = b) :
    ∃ u, K.Adj b u ∧ u ∈ sideVerts K P S := by
  induction w with
  | nil => exact absurd rfl hab
  | @cons a c b h p ih =>
    by_cases hcb : c = b
    · subst hcb
      exact ⟨a, h.symm, ha⟩
    · have hcS : c ∉ S := fun hc => hcb (hS c (by simp) hc)
      exact ih (sideVerts_extend K P S ha h hcS) hcb (fun y hy hyS => hS y (by simp [hy]) hyS)

theorem nbr_sv {V : Type*} [DecidableEq V] (K : SimpleGraph V) (P Q S : Finset V) (n : ℕ)
    (hn : NPointConnected K P Q n) (hS : Separates K P Q S) (hcard : S.card = n)
    {s : V} (hsS : s ∈ S) (hsP : s ∉ P) :
    ∃ u, K.Adj s u ∧ u ∈ sideVerts K P S := by
  have hns : ¬ Separates K P Q (S.erase s) := by
    intro h
    have := hn _ h
    rw [Finset.card_erase_of_mem hsS] at this
    have : 0 < S.card := Finset.card_pos.mpr ⟨s, hsS⟩
    omega
  unfold Separates at hns
  push_neg at hns
  obtain ⟨x, hx, y, hy, w, hw⟩ := hns
  have hsw : s ∈ w.support := by
    obtain ⟨v, hv, hvS⟩ := hS x hx y hy w
    have : v = s := by
      by_contra hne
      exact hw v hv (Finset.mem_erase.mpr ⟨hne, hvS⟩)
    exact this ▸ hv
  have hxs : x ≠ s := fun h => hsP (h ▸ hx)
  refine nbr_walk K P S (w.takeUntil s hsw) (sideVerts_of_P K P S hx ?_) hxs ?_
  · intro hxS
    exact hw x w.start_mem_support (Finset.mem_erase.mpr ⟨hxs, hxS⟩)
  · intro z hz hzS
    by_contra hne
    exact hw z (w.support_takeUntil_subset hsw hz) (Finset.mem_erase.mpr ⟨hne, hzS⟩)

theorem menger_aux {V : Type*} [Fintype V] [DecidableEq V] :
    ∀ (m : ℕ) (G : SimpleGraph V) (P Q : Finset V), Disjoint P Q → ∀ n : ℕ,
      G.edgeSet.ncard = m → NPointConnected G P Q n → HasDisjointPaths G P Q n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro G P Q hPQ n hm hG
  classical
  obtain ⟨K, hKG, hirr⟩ := exists_irreducible_part_core G P Q hPQ n hG
  apply lift_paths hKG
  have hKm : K.edgeSet.ncard ≤ m := hm ▸ Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hKG)
    (Set.toFinite _)
  have hge := grad_ge_core K P Q hPQ n hirr.1
  by_cases hEq : K.edgeFinset.card = n
  · obtain ⟨a, b, w, h1, h2, _⟩ := grad_eq_consists_core K P Q hPQ n hirr.1 hEq
    exact ⟨a, b, w, h1, h2⟩
  · have hgrad : n < K.edgeFinset.card := lt_of_le_of_ne hge (Ne.symm hEq)
    obtain ⟨s, hsP, hsQ, t, hst⟩ := exists_vertex_not_mem_core K P Q hPQ n hirr hgrad
    obtain ⟨S, hsS, hScard, hSsep⟩ := exists_separator_through_core K P Q hPQ n hirr hgrad s hsP hsQ t hst
    have hQP : Disjoint Q P := hPQ.symm
    obtain ⟨u1, hu1, hu1sv⟩ := nbr_sv K P Q S n hirr.1 hSsep hScard hsS hsP
    obtain ⟨u2, hu2, hu2sv⟩ := nbr_sv K Q P S n (npc_symm K hirr.1) (sep_symm K hSsep) hScard hsS hsQ
    have hfin : K.edgeSet.Finite := Set.toFinite _
    have hlt1 : (sidePart K P S).edgeSet.ncard < m := by
      refine lt_of_lt_of_le ?_ hKm
      refine Set.ncard_lt_ncard ⟨fun e he => SimpleGraph.edgeSet_mono (sidePart_le K P S) he, ?_⟩ hfin
      intro hsub
      have : s(s, u2) ∈ (sidePart K P S).edgeSet := hsub hu2
      have h' : (sidePart K P S).Adj s u2 := this
      have h2 := h'.2.1
      rcases h2 with h2 | h2
      · exact sideVerts_not_mem K P S h2 hsS
      · exact sideVerts_disjoint K P Q S hSsep h2 hu2sv
    have hlt2 : (sidePart K Q S).edgeSet.ncard < m := by
      refine lt_of_lt_of_le ?_ hKm
      refine Set.ncard_lt_ncard ⟨fun e he => SimpleGraph.edgeSet_mono (sidePart_le K Q S) he, ?_⟩ hfin
      intro hsub
      have : s(s, u1) ∈ (sidePart K Q S).edgeSet := hsub hu1
      have h' : (sidePart K Q S).Adj s u1 := this
      have h2 := h'.2.1
      rcases h2 with h2 | h2
      · exact sideVerts_not_mem K Q S h2 hsS
      · exact sideVerts_disjoint K P Q S hSsep hu1sv h2
    have hP := ih _ hlt1 (sidePart K P S) (P \ S) (S \ P)
      (Finset.disjoint_left.mpr fun x hx hx' => (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1)
      (n - (S ∩ P).card) rfl (side_npoint_connected_core K P Q hPQ n hirr.1 S hSsep hScard)
    have hQ := ih _ hlt2 (sidePart K Q S) (Q \ S) (S \ Q)
      (Finset.disjoint_left.mpr fun x hx hx' => (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1)
      (n - (S ∩ Q).card) rfl
      (side_npoint_connected_core K Q P hQP n (npc_symm K hirr.1) S (sep_symm K hSsep) hScard)
    exact glue_paths_core K P Q hPQ n S hSsep hScard hP hQ

theorem satz_delta_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n) :
    HasDisjointPaths G P Q n :=
  menger_aux _ G P Q hPQ n rfl hG

end Menger27.Graphs

open Menger27.Graphs


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n) :
    HasDisjointPaths G P Q n := by
  exact satz_delta_core G P Q hPQ n hG
