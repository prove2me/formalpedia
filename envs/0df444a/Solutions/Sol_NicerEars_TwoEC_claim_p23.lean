-- Prove2me | solution 1 for NicerEars.TwoEC.claim_p23
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:13:09.859557+00:00
-- url     : https://prove2.me/submissions/deef1967-dca3-49db-a9ac-3cfe45225179

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Earmuff

set_option linter.unusedSectionVars false

namespace NicerEars.TwoEC.Aux30

open Finset NicerEars.TwoEC

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma spanGraph_adj (G : Graph V E) (F : Finset E) (u w : V) :
    (G.spanGraph F).Adj u w ↔ u ≠ w ∧ ∃ e ∈ F, G.ends e = s(u, w) := by
  simp only [Graph.spanGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image, Finset.mem_coe]
  tauto

lemma mem_cut (G : Graph V E) (W : Finset V) (e : E) :
    e ∈ G.cut W ↔ ∃ u ∈ W, ∃ v ∉ W, G.ends e = s(u, v) := by
  simp [Graph.cut]

lemma ends_eq (G : Graph V E) (e : E) : ∃ a b, a ≠ b ∧ G.ends e = s(a, b) := by
  have key : ∀ z : Sym2 V, ¬ z.IsDiag → ∃ a b, a ≠ b ∧ z = s(a, b) := by
    intro z
    induction z using Sym2.ind with
    | _ a b => intro h; exact ⟨a, b, by simpa using h, rfl⟩
  exact key _ (G.loopless e)

lemma mem_cut_singleton (G : Graph V E) (v : V) (e : E) :
    e ∈ G.cut {v} ↔ v ∈ G.ends e := by
  rw [mem_cut]
  obtain ⟨a, b, hab, h⟩ := ends_eq G e
  rw [h]
  constructor
  · rintro ⟨u, hu, w, hw, h'⟩
    rw [mem_singleton] at hu; subst hu
    rw [h']; exact Sym2.mem_mk_left _ _
  · intro hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ⟨v, mem_singleton_self _, b, by simpa [eq_comm] using hab, rfl⟩
    · exact ⟨v, mem_singleton_self _, a, by simpa using hab, Sym2.eq_swap⟩

lemma connected_iff_cut (G : Graph V E) (F : Finset E) [Nonempty V] :
    (G.spanGraph F).Connected ↔
      ∀ W : Finset V, W.Nonempty → W ≠ univ → ∃ e ∈ F, e ∈ G.cut W := by
  constructor
  · intro hc W ⟨u, hu⟩ hW
    obtain ⟨w, hw⟩ : ∃ w, w ∉ W := by
      by_contra h; push Not at h; exact hW (eq_univ_iff_forall.mpr h)
    obtain ⟨p⟩ := hc.preconnected u w
    obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (W : Set V) hu hw
    have hadj := d.adj
    rw [spanGraph_adj] at hadj
    obtain ⟨-, e, he, hends⟩ := hadj
    exact ⟨e, he, (mem_cut G W e).2 ⟨_, hd1, _, hd2, hends⟩⟩
  · intro h
    rw [SimpleGraph.connected_iff]
    refine ⟨?_, inferInstance⟩
    intro u w
    by_contra hnr
    classical
    let W : Finset V := univ.filter (fun z => (G.spanGraph F).Reachable u z)
    have hWne : W.Nonempty := ⟨u, by simp [W]⟩
    have hWu : W ≠ univ := by
      intro hh
      have : w ∈ W := hh ▸ mem_univ w
      simp [W] at this
      exact hnr this
    obtain ⟨e, he, hcut⟩ := h W hWne hWu
    obtain ⟨a, ha, b, hb, hends⟩ := (mem_cut G W e).1 hcut
    have hab : a ≠ b := fun hab => hb (hab ▸ ha)
    have hadj : (G.spanGraph F).Adj a b := (spanGraph_adj G F a b).2 ⟨hab, e, he, hends⟩
    simp only [W, mem_filter, mem_univ, true_and] at ha hb
    exact hb (ha.trans hadj.reachable)

lemma twoEC_iff_cut (G : Graph V E) (F : Finset E) [Nonempty V] :
    G.IsTwoECSpanning F ↔
      ∀ W : Finset V, W.Nonempty → W ≠ univ →
        ∃ e₁ ∈ F, ∃ e₂ ∈ F, e₁ ≠ e₂ ∧ e₁ ∈ G.cut W ∧ e₂ ∈ G.cut W := by
  unfold Graph.IsTwoECSpanning
  simp only [connected_iff_cut]
  constructor
  · rintro ⟨h1, h2⟩ W hW hWu
    obtain ⟨e, he, hc⟩ := h1 W hW hWu
    obtain ⟨e', he', hc'⟩ := h2 e he W hW hWu
    rw [mem_erase] at he'
    exact ⟨e, he, e', he'.2, he'.1.symm, hc, hc'⟩
  · intro h
    refine ⟨fun W hW hWu => ?_, fun e he W hW hWu => ?_⟩
    · obtain ⟨e, he, -, -, -, hc, -⟩ := h W hW hWu
      exact ⟨e, he, hc⟩
    · obtain ⟨e₁, he₁, e₂, he₂, hne, hc₁, hc₂⟩ := h W hW hWu
      by_cases h1 : e₁ = e
      · exact ⟨e₂, mem_erase.2 ⟨fun h2 => hne (h1.trans h2.symm), he₂⟩, hc₂⟩
      · exact ⟨e₁, mem_erase.2 ⟨h1, he₁⟩, hc₁⟩

lemma cut_of_ends (G : Graph V E) (W : Finset V) (e : E) (u w : V) (h : G.ends e = s(u, w))
    (hu : u ∈ W) (hw : w ∉ W) : e ∈ G.cut W := (mem_cut G W e).2 ⟨u, hu, w, hw, h⟩

lemma cut_of_ends' (G : Graph V E) (W : Finset V) (e : E) (u w : V) (h : G.ends e = s(u, w))
    (hu : u ∉ W) (hw : w ∈ W) : e ∈ G.cut W :=
  (mem_cut G W e).2 ⟨w, hw, u, hu, h.trans Sym2.eq_swap⟩

lemma ne_of_ends (G : Graph V E) (e e' : E) (p q : Sym2 V) (h : G.ends e = p) (h' : G.ends e' = q)
    (hpq : p ≠ q) : e ≠ e' := by
  rintro rfl; exact hpq (h.symm.trans h')



lemma cut_iff_of_ends (G : Graph V E) (W : Finset V) (e : E) (p q : V) (h : G.ends e = s(p, q)) :
    e ∈ G.cut W ↔ (p ∈ W ∧ q ∉ W) ∨ (q ∈ W ∧ p ∉ W) := by
  rw [mem_cut]
  constructor
  · rintro ⟨u, hu, w, hw, h'⟩
    rw [h, Sym2.eq_iff] at h'
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hu, hw⟩
    · exact Or.inr ⟨hu, hw⟩
  · rintro (⟨hp, hq⟩ | ⟨hq, hp⟩)
    · exact ⟨p, hp, q, hq, h⟩
    · exact ⟨q, hq, p, hp, h.trans Sym2.eq_swap⟩

/-! ### Counting over an ear-decomposition -/

lemma card_edges (G : Graph V E) (P : Ear G) : #P.edges = P.len := by
  unfold Ear.edges
  rw [card_image_of_injective _ P.edge_inj, card_univ, Fintype.card_fin]

lemma card_inner (G : Graph V E) (P : Ear G) : #P.inner = P.len - 1 := by
  unfold Ear.inner
  rw [card_image_of_injOn]
  · have : (univ.filter (fun i : Fin (P.len + 1) => 0 < i.val ∧ i.val < P.len)).map
        Fin.valEmbedding = Finset.Ioo 0 P.len := by
      ext n
      simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_Ioo]
      constructor
      · rintro ⟨i, h, rfl⟩; exact h
      · intro h; exact ⟨⟨n, by omega⟩, h, rfl⟩
    rw [← card_map Fin.valEmbedding, this, Nat.card_Ioo]
    simp
  · intro i hi j hj hij
    simp only [coe_filter, mem_univ, true_and] at hi hj
    rcases P.vert_inj i j hij with h | h
    · exact h
    · exfalso
      have h0 : (0 : Fin (P.len + 1)) ∈ ({i, j} : Set (Fin (P.len + 1))) := by
        rw [h]; exact Set.mem_insert _ _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0
      rcases h0 with h0 | h0
      · have := hi.1; rw [← h0] at this; simp at this
      · have := hj.1; rw [← h0] at this; simp at this

lemma inner_subset_verts (G : Graph V E) (P : Ear G) : P.inner ⊆ P.verts :=
  image_subset_image (subset_univ _)

lemma inner_disjoint (G : Graph V E) (D : EarDecomposition G) (i j : Fin D.k) (hij : i ≠ j) :
    Disjoint (D.ear i).inner (D.ear j).inner := by
  have aux : ∀ i j : Fin D.k, j < i → Disjoint (D.ear i).inner (D.ear j).inner := by
    intro i j hji
    refine (D.attach i).2.2.mono_right ?_
    refine (inner_subset_verts G _).trans ?_
    refine subset_trans ?_ (subset_insert _ _)
    exact subset_biUnion_of_mem (fun j => (D.ear j).verts) (by simpa using hji)
  rcases lt_or_gt_of_ne hij with h | h
  · exact (aux j i h).symm
  · exact aux i j h

lemma root_not_inner (G : Graph V E) (D : EarDecomposition G) (i : Fin D.k) :
    D.root ∉ (D.ear i).inner := fun h =>
  disjoint_left.1 (D.attach i).2.2 h (mem_insert_self _ _)

/-- Every non-root vertex is an internal vertex of the first ear containing it. -/
lemma mem_inner_of_ne_root (G : Graph V E) (D : EarDecomposition G) (v : V) (hv : v ≠ D.root) :
    ∃ i, v ∈ (D.ear i).inner := by
  classical
  have hex : ∃ i, v ∈ (D.ear i).verts := (D.vert_cover v).resolve_left hv
  let S := univ.filter (fun i => v ∈ (D.ear i).verts)
  have hS : S.Nonempty := by obtain ⟨i, hi⟩ := hex; exact ⟨i, by simp [S, hi]⟩
  obtain ⟨i, hiS, himin⟩ := S.exists_min_image id hS
  have hi : v ∈ (D.ear i).verts := (mem_filter.1 hiS).2
  have hmin : ∀ j, j < i → v ∉ (D.ear j).verts := by
    intro j hj hjv
    have : i ≤ j := himin j (by simp [S, hjv])
    exact absurd hj (not_lt.2 this)
  refine ⟨i, ?_⟩
  have hprev : v ∉ insert D.root ((univ.filter (· < i)).biUnion (fun j => (D.ear j).verts)) := by
    simp only [mem_insert, mem_biUnion, mem_filter, mem_univ, true_and, not_or, not_exists,
      not_and]
    exact ⟨hv, fun j hj => hmin j hj⟩
  unfold Ear.verts at hi
  obtain ⟨t, -, rfl⟩ := mem_image.1 hi
  unfold Ear.inner
  refine mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, rfl⟩
  · by_contra h0
    have ht : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    apply hprev; rw [ht]; exact (D.attach i).1
  · by_contra h0
    have ht : t = Fin.last _ := Fin.ext (by simp; omega)
    apply hprev; rw [ht]; exact (D.attach i).2.1

lemma sum_inner (G : Graph V E) (D : EarDecomposition G) :
    ∑ i, ((D.ear i).len - 1) = Fintype.card V - 1 := by
  classical
  have hU : univ.biUnion (fun i => (D.ear i).inner) = univ.erase D.root := by
    ext v
    simp only [mem_biUnion, mem_univ, true_and, mem_erase, and_true]
    constructor
    · rintro ⟨i, hi⟩ rfl; exact root_not_inner G D i hi
    · intro hv; exact mem_inner_of_ne_root G D v hv
  have := congrArg Finset.card hU
  rw [card_biUnion (fun i _ j _ hij => inner_disjoint G D i j hij), card_erase_of_mem (mem_univ _),
    card_univ] at this
  simpa [card_inner] using this


lemma edges_disjoint (G : Graph V E) (D : EarDecomposition G) (i j : Fin D.k) (hij : i ≠ j) :
    Disjoint (D.ear i).edges (D.ear j).edges := by
  rw [disjoint_left]
  intro e hi hj
  obtain ⟨l, -, hl⟩ := D.edge_part e
  exact hij ((hl i hi).trans (hl j hj).symm)

lemma ear_term (l : ℕ) (hl : 1 ≤ l) :
    (if 1 < l then (l : ℝ) else 0) ≤
      5 / 4 * ((l - 1 : ℕ) : ℝ) + 3 / 4 * (if Even l then 1 else 0) +
        1 / 2 * (if l = 3 then 1 else 0) := by
  by_cases h4 : l ≤ 4
  · interval_cases l <;> norm_num [Nat.even_iff]
  · push Not at h4
    rw [if_pos (by omega), Nat.cast_sub (by omega)]
    have h1 : (0 : ℝ) ≤ (if Even l then 1 else 0) := by split_ifs <;> norm_num
    have h2 : (0 : ℝ) ≤ (if l = 3 then 1 else 0) := by split_ifs <;> norm_num
    have : (5 : ℝ) ≤ l := by exact_mod_cast h4
    push_cast
    nlinarith

lemma claim_card (G : Graph V E) (D : EarDecomposition G) (hD : D.IsNice) :
    (#D.nontrivialEdges : ℝ) ≤ 5 / 4 * (Lphi G : ℝ) + 1 / 2 * D.numPendant := by
  classical
  have hne : Nonempty V := ⟨D.root⟩
  have hcard : #D.nontrivialEdges = ∑ i ∈ univ.filter (fun i => (D.ear i).IsNontrivial),
      (D.ear i).len := by
    unfold EarDecomposition.nontrivialEdges
    rw [card_biUnion (fun i _ j _ hij => edges_disjoint G D i j hij)]
    simp [card_edges]
  have hterm : ∀ i : Fin D.k, (if (D.ear i).IsNontrivial then ((D.ear i).len : ℝ) else 0) ≤
      5 / 4 * (((D.ear i).len - 1 : ℕ) : ℝ) + 3 / 4 * (if (D.ear i).IsEven then 1 else 0) +
        1 / 2 * (if (D.ear i).len = 3 then 1 else 0) := by
    intro i
    have := ear_term (D.ear i).len (D.ear i).len_pos
    convert this using 2 <;> try rfl
    simp only [Ear.IsEven]
    by_cases h : Even (D.ear i).len <;> simp [h]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin D.k))) => hterm i)
  rw [← Finset.sum_filter, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    Finset.sum_boole, Finset.sum_boole] at hsum
  have hs : ∑ i, (((D.ear i).len - 1 : ℕ) : ℝ) = ((Fintype.card V - 1 : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, sum_inner G D]
  rw [hs] at hsum
  have hc : (#D.nontrivialEdges : ℝ) = ((∑ i ∈ univ.filter (fun i => (D.ear i).IsNontrivial),
      (D.ear i).len : ℕ) : ℝ) := by rw [hcard]
  have hev : (#(univ.filter (fun i => (D.ear i).IsEven)) : ℝ) = G.phi := by
    have := hD.1
    unfold EarDecomposition.numEven at this
    exact_mod_cast this
  have h3 : #(univ.filter (fun i => (D.ear i).len = 3)) ≤ D.numPendant := by
    unfold EarDecomposition.numPendant
    apply card_le_card
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hD.2.1 i (Or.inr hi)
  have h3' : (#(univ.filter (fun i => (D.ear i).len = 3)) : ℝ) ≤ D.numPendant := by
    exact_mod_cast h3
  have hn : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [Nat.cast_sub Fintype.card_pos]; simp
  have hphi : (0 : ℝ) ≤ G.phi := Nat.cast_nonneg _
  unfold Lphi
  push_cast
  rw [hc]
  rw [hn, hev] at hsum
  push_cast at hsum ⊢
  linarith

/-! ### The nontrivial ears form a 2-edge-connected spanning subgraph -/

lemma nat_ivt (f : ℕ → Prop) (a b : ℕ) (hab : a ≤ b) (ha : ¬ f a) (hb : f b) :
    ∃ k, a ≤ k ∧ k < b ∧ ¬ f k ∧ f (k + 1) := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact absurd hb ha
  | succ b ih =>
    by_cases hb' : f b
    · by_cases hab' : a ≤ b
      · obtain ⟨k, h1, h2, h3, h4⟩ := ih hab' hb'
        exact ⟨k, h1, by omega, h3, h4⟩
      · have : a = b + 1 := by omega
        subst this; exact absurd hb ha
    · by_cases hab' : a ≤ b
      · exact ⟨b, hab', by omega, hb', hb⟩
      · have : a = b + 1 := by omega
        subst this; exact absurd hb ha

lemma twoEC_nontrivial (G : Graph V E) (D : EarDecomposition G) :
    G.IsTwoECSpanning D.nontrivialEdges := by
  classical
  have hne : Nonempty V := ⟨D.root⟩
  rw [twoEC_iff_cut]
  intro W hW hWu
  let side : V → Prop := fun z => (z ∈ W ↔ D.root ∈ W)
  have hex : ∃ i, ∃ t, ¬ side ((D.ear i).vert t) := by
    by_contra hall
    push Not at hall
    have hall' : ∀ z, side z := by
      intro z
      rcases D.vert_cover z with rfl | ⟨i, hi⟩
      · exact Iff.rfl
      · unfold Ear.verts at hi
        obtain ⟨t, -, rfl⟩ := mem_image.1 hi
        exact hall i t
    by_cases hr : D.root ∈ W
    · apply hWu; apply eq_univ_iff_forall.mpr; intro z; exact (hall' z).2 hr
    · obtain ⟨z, hz⟩ := hW; exact hr ((hall' z).1 hz)
  let S := univ.filter (fun i => ∃ t, ¬ side ((D.ear i).vert t))
  have hS : S.Nonempty := by obtain ⟨i, hi⟩ := hex; exact ⟨i, by simp [S, hi]⟩
  obtain ⟨i, hiS, himin⟩ := S.exists_min_image id hS
  obtain ⟨t, ht⟩ := (mem_filter.1 hiS).2
  have hprev : ∀ z ∈ insert D.root ((univ.filter (· < i)).biUnion (fun j => (D.ear j).verts)),
      side z := by
    intro z hz
    rcases mem_insert.1 hz with rfl | hz
    · exact Iff.rfl
    · obtain ⟨j, hj, hzj⟩ := mem_biUnion.1 hz
      simp only [mem_filter, mem_univ, true_and] at hj
      by_contra hzs
      unfold Ear.verts at hzj
      obtain ⟨t', -, rfl⟩ := mem_image.1 hzj
      have : i ≤ j := himin j (by simp only [S, mem_filter, mem_univ, true_and]; exact ⟨t', hzs⟩)
      exact absurd hj (not_lt.2 this)
  have hfirst : side ((D.ear i).vert 0) := hprev _ (D.attach i).1
  have hlast : side ((D.ear i).vert (Fin.last (D.ear i).len)) := hprev _ (D.attach i).2.1
  let g : ℕ → V := fun n => (D.ear i).vert ⟨min n (D.ear i).len, by omega⟩
  have hg : ∀ (n : ℕ) (h : n < (D.ear i).len + 1), g n = (D.ear i).vert ⟨n, h⟩ := by
    intro n h; simp only [g]; congr; omega
  let f : ℕ → Prop := fun n => ¬ side (g n)
  have f0 : ¬ f 0 := by
    simp only [f, not_not]; rw [hg 0 (by omega)]; exact hfirst
  have ft : f t.val := by simp only [f]; rw [hg t.val t.isLt]; exact ht
  have fl : ¬ f (D.ear i).len := by
    simp only [f, not_not]; rw [hg (D.ear i).len (by omega)]; exact hlast
  have htl : t.val < (D.ear i).len := by
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 t.isLt) with h | h
    · exact h
    · exfalso; exact fl (h ▸ ft)
  obtain ⟨k, -, hk, hk1, hk2⟩ := nat_ivt f 0 t.val (by omega) f0 ft
  obtain ⟨m, hm0, hm, hm1, hm2⟩ := nat_ivt (fun n => ¬ f n) t.val (D.ear i).len htl.le
    (by simpa using ft) (by simpa using fl)
  simp only [not_not] at hm1
  have cross : ∀ (j : ℕ) (hj : j < (D.ear i).len), (f j ↔ ¬ f (j + 1)) →
      (D.ear i).edge ⟨j, hj⟩ ∈ G.cut W := by
    intro j hj hiff
    have hlink := (D.ear i).link ⟨j, hj⟩
    have e1 : (D.ear i).vert (Fin.castSucc ⟨j, hj⟩) = g j := (hg j (by omega)).symm
    have e2 : (D.ear i).vert (Fin.succ ⟨j, hj⟩) = g (j + 1) := by
      rw [hg (j + 1) (by omega)]; rfl
    rw [e1, e2] at hlink
    rw [cut_iff_of_ends G W _ _ _ hlink]
    simp only [f, side] at hiff
    generalize g j = A at hiff ⊢
    generalize g (j + 1) = B at hiff ⊢
    by_cases a : A ∈ W <;> by_cases b : B ∈ W <;> by_cases c : D.root ∈ W <;> simp_all
  have hmem : ∀ (j : ℕ) (hj : j < (D.ear i).len), (D.ear i).edge ⟨j, hj⟩ ∈ D.nontrivialEdges := by
    intro j hj
    unfold EarDecomposition.nontrivialEdges
    refine mem_biUnion.2 ⟨i, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      show 1 < (D.ear i).len
      omega
    · unfold Ear.edges; exact mem_image_of_mem _ (mem_univ _)
  refine ⟨(D.ear i).edge ⟨k, by omega⟩, hmem _ _, (D.ear i).edge ⟨m, hm⟩, hmem _ _, ?_,
    cross k _ (iff_of_false hk1 (not_not.2 hk2)), cross m hm (iff_of_true hm1 hm2)⟩
  intro h
  have := (D.ear i).edge_inj h
  simp only [Fin.mk.injEq] at this
  omega

end NicerEars.TwoEC.Aux30

open Finset NicerEars.TwoEC.Aux30 in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TwoEC.Graph V E) (D : NicerEars.TwoEC.EarDecomposition G) (hD : D.IsNice) :
    G.IsTwoECSpanning D.nontrivialEdges ∧
      (#D.nontrivialEdges : ℝ) ≤ 5 / 4 * (NicerEars.TwoEC.Lphi G : ℝ) + 1 / 2 * D.numPendant :=
  ⟨twoEC_nontrivial G D, claim_card G D hD⟩
