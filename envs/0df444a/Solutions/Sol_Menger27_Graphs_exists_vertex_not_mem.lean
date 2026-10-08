-- Prove2me | solution 1 for Menger27.Graphs.exists_vertex_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T05:59:25.273044+00:00
-- url     : https://prove2.me/submissions/aee10d0e-cebb-4c6a-b31b-3d512fa77466

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts



namespace Menger27.Graphs

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

end Menger27.Graphs

open Menger27.Graphs


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hK : IrreduciblyNPointConnected K P Q n) (hgrad : n < K.edgeFinset.card) :
    ∃ s : V, s ∉ P ∧ s ∉ Q ∧ ∃ t : V, K.Adj s t := by
  exact exists_vertex_not_mem_core K P Q hPQ n hK hgrad
