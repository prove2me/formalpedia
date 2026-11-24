-- Prove2me | solution 1 for GraphIsoTesting.FixedGraph.padding_distance_loss
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T01:41:59.314267+00:00
-- url     : https://prove2.me/submissions/b7ee1c5a-0910-4613-8ef0-54f860132ae5

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_Padding

open GraphIsoTesting.FixedGraph

theorem gi_adj {V : Type} (G : SimpleGraph V) (r : ℕ) (x y : V ⊕ Fin r) :
    (isolatedPadding G r).Adj x y ↔ ∃ u v, x = Sum.inl u ∧ y = Sum.inl v ∧ G.Adj u v := by
  simp only [isolatedPadding, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨u, v, rfl, rfl, h⟩ | ⟨u, v, rfl, rfl, h⟩⟩
    · exact ⟨u, v, rfl, rfl, h⟩
    · exact ⟨v, u, rfl, rfl, h.symm⟩
  · rintro ⟨u, v, rfl, rfl, h⟩
    exact ⟨fun e => h.ne (Sum.inl_injective e), Or.inl ⟨u, v, rfl, rfl, h⟩⟩

theorem gi_count {α β : Type} (S D : Finset α) (B : Finset β) (ι : α ↪ β)
    (h : ∀ x ∈ S, x ∈ D ∨ ι x ∈ B) : S.card ≤ B.card + D.card := by
  classical
  calc S.card ≤ (S.filter (fun x => ι x ∈ B) ∪ D).card := by
        apply Finset.card_le_card
        intro x hx
        rcases h x hx with h1 | h1
        · exact Finset.mem_union_right _ h1
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hx, h1⟩)
    _ ≤ (S.filter (fun x => ι x ∈ B)).card + D.card := Finset.card_union_le _ _
    _ ≤ B.card + D.card := by
        apply Nat.add_le_add_right
        exact Finset.card_le_card_of_injOn ι (fun x hx => (Finset.mem_filter.1 hx).2)
          ι.injective.injOn

theorem solution {V : Type} [Fintype V]
    (G H : SimpleGraph V) (d r : ℕ) (hG : DegreeBound G d) (hH : DegreeBound H d) :
    isoDistance G H ≤ isoDistance (isolatedPadding G r) (isolatedPadding H r) + 4 * d * r := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (V ⊕ Fin r),
      isoDistance (isolatedPadding G r) (isolatedPadding H r) =
        edgeMismatch (isolatedPadding G r) (isolatedPadding H r) σ := by
    unfold isoDistance
    exact (Finset.exists_mem_eq_inf' _ _).imp fun σ h => h.2
  let p : V → Prop := fun v => ∃ w, σ (Sum.inl v) = Sum.inl w
  let q : V → Prop := fun w => ∃ v, σ.symm (Sum.inl w) = Sum.inl v
  let f : {v // p v} → {w // q w} := fun v => ⟨Classical.choose v.2, ⟨v.1, by
      rw [← Classical.choose_spec v.2, Equiv.symm_apply_apply]⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 := Classical.choose_spec a.2
      have h2 := Classical.choose_spec b.2
      have h3 : Classical.choose a.2 = Classical.choose b.2 := congrArg Subtype.val hab
      apply Subtype.ext
      apply Sum.inl_injective
      apply σ.injective
      rw [h1, h2, h3]
    · rintro ⟨w, v, hv⟩
      have hp : p v := ⟨w, by rw [← hv, Equiv.apply_symm_apply]⟩
      refine ⟨⟨v, hp⟩, Subtype.ext ?_⟩
      have h1 := Classical.choose_spec hp
      apply Sum.inl_injective
      show Sum.inl (Classical.choose hp) = Sum.inl w
      rw [← h1, ← hv, Equiv.apply_symm_apply]
  let π : Equiv.Perm V := (Equiv.ofBijective f hf).extendSubtype
  have hπ : ∀ v, p v → σ (Sum.inl v) = Sum.inl (π v) := by
    intro v hv
    have h := Equiv.extendSubtype_apply_of_mem (Equiv.ofBijective f hf) v hv
    rw [h]
    exact Classical.choose_spec hv
  let A := Finset.univ.filter (fun v => ¬ p v)
  have hA : A.card ≤ r := by
    have hinj : Function.Injective (fun v => σ (Sum.inl v)) := σ.injective.comp Sum.inl_injective
    rw [← Finset.card_image_of_injective A hinj]
    calc (A.image fun v => σ (Sum.inl v)).card ≤
          (Finset.univ.map Function.Embedding.inr : Finset (V ⊕ Fin r)).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, A] at hx
          obtain ⟨v, hv, rfl⟩ := hx
          simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.inr_apply]
          cases h : σ (Sum.inl v) with
          | inl w => exact absurd ⟨w, h⟩ hv
          | inr j => exact ⟨j, rfl⟩
      _ = r := by simp
  let Dset := G.edgeFinset.filter (fun e => ∃ v ∈ e, ¬ p v)
  have hD : Dset.card ≤ d * r := by
    calc Dset.card ≤ (A.biUnion fun v => (G.neighborFinset v).image fun w => s(v, w)).card := by
          apply Finset.card_le_card
          intro e he
          simp only [Dset, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
          obtain ⟨he, v, hv, hpv⟩ := he
          simp only [Finset.mem_biUnion, Finset.mem_image, SimpleGraph.mem_neighborFinset, A,
            Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨v, hpv, ?_⟩
          induction e using Sym2.ind with
          | h a b =>
            rw [SimpleGraph.mem_edgeSet] at he
            rcases Sym2.mem_iff.1 hv with rfl | rfl
            · exact ⟨b, he, rfl⟩
            · exact ⟨a, he.symm, Sym2.eq_swap⟩
      _ ≤ ∑ v ∈ A, ((G.neighborFinset v).image fun w => s(v, w)).card := Finset.card_biUnion_le
      _ ≤ ∑ v ∈ A, d := by
          apply Finset.sum_le_sum
          intro v _
          refine Finset.card_image_le.trans ?_
          have h := hG v
          convert h using 2
      _ = A.card * d := by simp
      _ ≤ d * r := by rw [mul_comm]; exact Nat.mul_le_mul_left d hA
  have h1 : isoDistance G H ≤ edgeMismatch G H π := by
    unfold isoDistance
    exact Finset.inf'_le _ (Finset.mem_univ _)
  let ι : Sym2 V ↪ Sym2 (V ⊕ Fin r) := ⟨Sym2.map Sum.inl, Sym2.map.injective Sum.inl_injective⟩
  have hmain : edgeMismatch G H π ≤
      edgeMismatch (isolatedPadding G r) (isolatedPadding H r) σ + Dset.card := by
    unfold edgeMismatch
    dsimp only
    refine (gi_count _ (Dset.image (Sym2.map π)) _ ι ?_).trans
      (Nat.add_le_add_left Finset.card_image_le _)
    intro x hx
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_image] at hx
    rcases hx with ⟨⟨e, he, rfl⟩, hxH⟩ | ⟨hxH, hxT⟩
    · have he' : e ∈ G.edgeSet := by simpa only [SimpleGraph.mem_edgeFinset] using he
      by_cases hD' : ∃ v ∈ e, ¬ p v
      · exact Or.inl (Finset.mem_image.2
          ⟨e, Finset.mem_filter.2 ⟨SimpleGraph.mem_edgeFinset.2 he', hD'⟩, rfl⟩)
      · push Not at hD'
        right
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_image]
        refine Or.inl ⟨?_, ?_⟩
        · refine ⟨Sym2.map Sum.inl e, ?_, ?_⟩
          · induction e using Sym2.ind with
            | h a b =>
              simp only [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
              rw [SimpleGraph.mem_edgeSet] at he'
              exact (gi_adj G r _ _).2 ⟨a, b, rfl, rfl, he'⟩
          · induction e using Sym2.ind with
            | h a b =>
              have ha := hD' a (Sym2.mem_mk_left a b)
              have hb := hD' b (Sym2.mem_mk_right a b)
              simp only [Sym2.map_mk, ι, Function.Embedding.coeFn_mk, hπ a ha, hπ b hb]
        · induction e using Sym2.ind with
          | h a b =>
            simp only [ι, Function.Embedding.coeFn_mk, Sym2.map_mk, SimpleGraph.mem_edgeFinset,
              SimpleGraph.mem_edgeSet, gi_adj] at hxH ⊢
            rintro ⟨u, v, h1, h2, h3⟩
            obtain rfl := Sum.inl_injective h1
            obtain rfl := Sum.inl_injective h2
            exact hxH h3
    · right
      simp only [Finset.mem_union, Finset.mem_sdiff]
      refine Or.inr ⟨?_, ?_⟩
      · induction x using Sym2.ind with
        | h a b =>
          simp only [ι, Function.Embedding.coeFn_mk, Sym2.map_mk, SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet] at hxH ⊢
          exact (gi_adj H r _ _).2 ⟨a, b, rfl, rfl, hxH⟩
      · induction x using Sym2.ind with
        | h a b =>
          simp only [Finset.mem_image]
          rintro ⟨e', he', heq⟩
          induction e' using Sym2.ind with
          | h y1 y2 =>
            simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, gi_adj] at he'
            obtain ⟨u1, u2, rfl, rfl, hu⟩ := he'
            simp only [ι, Function.Embedding.coeFn_mk, Sym2.map_mk, Sym2.eq_iff] at heq
            apply hxT
            refine ⟨s(u1, u2), SimpleGraph.mem_edgeFinset.2 hu, ?_⟩
            rw [Sym2.map_mk]
            rcases heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · have f1 : π u1 = a := Sum.inl_injective ((hπ u1 ⟨a, e1⟩).symm.trans e1)
              have f2 : π u2 = b := Sum.inl_injective ((hπ u2 ⟨b, e2⟩).symm.trans e2)
              rw [f1, f2]
            · have f1 : π u1 = b := Sum.inl_injective ((hπ u1 ⟨b, e1⟩).symm.trans e1)
              have f2 : π u2 = a := Sum.inl_injective ((hπ u2 ⟨a, e2⟩).symm.trans e2)
              rw [f1, f2, Sym2.eq_swap]
  calc isoDistance G H ≤ edgeMismatch G H π := h1
    _ ≤ edgeMismatch (isolatedPadding G r) (isolatedPadding H r) σ + Dset.card := hmain
    _ ≤ isoDistance (isolatedPadding G r) (isolatedPadding H r) + d * r := by
        rw [hσ]; exact Nat.add_le_add_left hD _
    _ ≤ _ := Nat.add_le_add_left (by
        rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ (by norm_num)) _
