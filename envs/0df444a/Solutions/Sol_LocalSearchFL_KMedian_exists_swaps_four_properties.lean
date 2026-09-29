-- Prove2me | solution 1 for LocalSearchFL.KMedian.exists_swaps_four_properties
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:54:27.014067+00:00
-- url     : https://prove2.me/submissions/0ca38ef7-9bfa-45ce-bb21-29f861a59def

import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_captures



namespace LocalSearchFL.KMedian

theorem cap_unique {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (s t o : Fa) (hs : captures σS σO s o) (ht : captures σS σO t o) :
    s = t := by
  by_contra hne
  unfold captures at hs ht
  have hd : Disjoint (nbhd σO o ∩ nbhd σS s) (nbhd σO o ∩ nbhd σS t) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [nbhd, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hne (h1.2.symm.trans h2.2)
  have h1 := Finset.card_union_of_disjoint hd
  have h2 := Finset.card_le_card (show (nbhd σO o ∩ nbhd σS s) ∪ (nbhd σO o ∩ nbhd σS t) ⊆
    nbhd σO o from Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
  omega

theorem sw4_core {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O : Finset Fa) (hcard : S.card = O.card) :
    ∃ η : Fa → Fa,
      (∀ o ∈ O, η o ∈ S) ∧
      (∀ s ∈ S, (∃ o₁ ∈ O, ∃ o₂ ∈ O, o₁ ≠ o₂ ∧ captures σS σO s o₁ ∧ captures σS σO s o₂) →
        ∀ o ∈ O, η o ≠ s) ∧
      (∀ s ∈ S, IsGood σS σO O s → (O.filter (fun o => η o = s)).card ≤ 2) ∧
      (∀ o ∈ O, ∀ o' ∈ O, o' ≠ o → ¬ captures σS σO (η o) o') := by
  classical
  let C : Fa → Finset Fa := fun s => O.filter (fun o => captures σS σO s o)
  have hC : ∀ s o, o ∈ C s ↔ o ∈ O ∧ captures σS σO s o := fun s o => Finset.mem_filter
  have hdisj : ∀ s t, s ≠ t → Disjoint (C s) (C t) := by
    intro s t hst
    rw [Finset.disjoint_left]
    intro o h1 h2
    exact hst (cap_unique σS σO s t o ((hC _ _).mp h1).2 ((hC _ _).mp h2).2)
  let G := S.filter (fun s => (C s).card = 0)
  let B1 := S.filter (fun s => (C s).card = 1)
  let Bm := S.filter (fun s => 2 ≤ (C s).card)
  let P : Fa → Prop := fun o => ∃ s ∈ S, (C s).card = 1 ∧ o ∈ C s
  let Orest := O.filter (fun o => ¬ P o)
  -- counting
  have hS3 : S.card = G.card + B1.card + Bm.card := by
    have e1 : S = (G ∪ B1) ∪ Bm := by
      ext s; simp only [G, B1, Bm, Finset.mem_union, Finset.mem_filter]; constructor
      · intro h
        rcases Nat.lt_or_ge (C s).card 2 with h2 | h2
        · rcases Nat.lt_or_ge (C s).card 1 with h3 | h3
          · exact Or.inl (Or.inl ⟨h, by omega⟩)
          · exact Or.inl (Or.inr ⟨h, by omega⟩)
        · exact Or.inr ⟨h, h2⟩
      · intro h; rcases h with (h | h) | h <;> exact h.1
    have d1 : Disjoint G B1 := by
      rw [Finset.disjoint_left]; intro s h1 h2
      simp only [G, B1, Finset.mem_filter] at h1 h2; omega
    have d2 : Disjoint (G ∪ B1) Bm := by
      rw [Finset.disjoint_left]; intro s h1 h2
      simp only [G, B1, Bm, Finset.mem_filter, Finset.mem_union] at h1 h2; omega
    conv_lhs => rw [e1]
    rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1]
  have hpd : ∀ X : Finset Fa, (X.biUnion C).card = ∑ s ∈ X, (C s).card := by
    intro X
    apply Finset.card_biUnion
    intro s _ t _ hst; exact hdisj s t hst
  have hB : B1.card + 2 * Bm.card ≤ O.card := by
    have hdB : Disjoint B1 Bm := by
      rw [Finset.disjoint_left]; intro s h1 h2
      simp only [B1, Bm, Finset.mem_filter] at h1 h2; omega
    have hsub : (B1 ∪ Bm).biUnion C ⊆ O := by
      intro o ho
      obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp ho
      exact ((hC _ _).mp hs).1
    have := Finset.card_le_card hsub
    rw [hpd, Finset.sum_union hdB] at this
    have e1 : ∑ s ∈ B1, (C s).card = B1.card := by
      rw [Finset.card_eq_sum_ones]; apply Finset.sum_congr rfl
      intro s hs; exact (Finset.mem_filter.mp hs).2
    have e2 : 2 * Bm.card ≤ ∑ s ∈ Bm, (C s).card := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum]; apply Finset.sum_le_sum
      intro s hs; have := (Finset.mem_filter.mp hs).2; omega
    omega
  have hO1 : B1.card ≤ (O.filter P).card := by
    have hsub : B1.biUnion C ⊆ O.filter P := by
      intro o ho
      obtain ⟨s, hs, hos⟩ := Finset.mem_biUnion.mp ho
      exact Finset.mem_filter.mpr ⟨((hC _ _).mp hos).1, s, (Finset.mem_filter.mp hs).1,
        (Finset.mem_filter.mp hs).2, hos⟩
    have := Finset.card_le_card hsub
    rw [hpd] at this
    have e1 : ∑ s ∈ B1, (C s).card = B1.card := by
      rw [Finset.card_eq_sum_ones]; apply Finset.sum_congr rfl
      intro s hs; exact (Finset.mem_filter.mp hs).2
    omega
  have hrest : Orest.card ≤ 2 * G.card := by
    have := Finset.card_filter_add_card_filter_not (s := O) (p := P)
    simp only [Orest]
    omega
  have hemb : Nonempty ({x // x ∈ Orest} ↪ {s // s ∈ G} × Fin 2) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    omega
  obtain ⟨e⟩ := hemb
  let η : Fa → Fa := fun o =>
    if h : P o then Classical.choose h
    else if h' : o ∈ O then (e ⟨o, Finset.mem_filter.mpr ⟨h', h⟩⟩).1.1 else o
  have hη1 : ∀ o (h : P o), η o = Classical.choose h ∧ Classical.choose h ∈ S ∧
      (C (Classical.choose h)).card = 1 ∧ o ∈ C (Classical.choose h) := by
    intro o h
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec h
    exact ⟨dif_pos h, h1, h2, h3⟩
  have hη2 : ∀ o (h : ¬ P o) (h' : o ∈ O),
      η o = (e ⟨o, Finset.mem_filter.mpr ⟨h', h⟩⟩).1.1 := by
    intro o h h'
    simp only [η, dif_neg h, dif_pos h']
  have hη2G : ∀ o (h : ¬ P o) (h' : o ∈ O), η o ∈ S ∧ (C (η o)).card = 0 := by
    intro o h h'
    rw [hη2 o h h']
    exact Finset.mem_filter.mp (e ⟨o, Finset.mem_filter.mpr ⟨h', h⟩⟩).1.2
  refine ⟨η, ?_, ?_, ?_, ?_⟩
  · intro o ho
    by_cases h : P o
    · obtain ⟨h1, h2, _⟩ := hη1 o h; rw [h1]; exact h2
    · exact (hη2G o h ho).1
  · intro s _ ⟨o₁, ho₁, o₂, ho₂, hne, hc1, hc2⟩ o ho heq
    have h2 : 2 ≤ (C s).card := by
      have : ({o₁, o₂} : Finset Fa) ⊆ C s := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact (hC _ _).mpr ⟨ho₁, hc1⟩
        · rw [Finset.mem_singleton.mp hx]; exact (hC _ _).mpr ⟨ho₂, hc2⟩
      have := Finset.card_le_card this
      rwa [Finset.card_pair hne] at this
    by_cases h : P o
    · obtain ⟨h1, _, h3, _⟩ := hη1 o h
      rw [← h1, heq] at h3; omega
    · have := (hη2G o h ho).2; rw [heq] at this; omega
  · intro s _ hgood
    have hC0 : C s = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro o ho; exact hgood o ((hC _ _).mp ho).1 ((hC _ _).mp ho).2
    let f : Fa → Fin 2 := fun o =>
      if h : o ∈ Orest then (e ⟨o, h⟩).2 else 0
    have hsubR : ∀ o ∈ O.filter (fun o => η o = s), ¬ P o ∧ o ∈ O := by
      intro o ho
      obtain ⟨hoO, hηs⟩ := Finset.mem_filter.mp ho
      refine ⟨fun h => ?_, hoO⟩
      obtain ⟨h1, _, _, h4⟩ := hη1 o h
      rw [← h1, hηs, hC0] at h4; simp at h4
    have hinj : Set.InjOn f (O.filter (fun o => η o = s)) := by
      intro a ha b hb hab
      obtain ⟨hPa, haO⟩ := hsubR a ha
      obtain ⟨hPb, hbO⟩ := hsubR b hb
      have hasR : a ∈ Orest := Finset.mem_filter.mpr ⟨haO, hPa⟩
      have hbsR : b ∈ Orest := Finset.mem_filter.mpr ⟨hbO, hPb⟩
      have ea := (Finset.mem_filter.mp ha).2
      have eb := (Finset.mem_filter.mp hb).2
      rw [hη2 a hPa haO] at ea
      rw [hη2 b hPb hbO] at eb
      simp only [f, dif_pos hasR, dif_pos hbsR] at hab
      have : e ⟨a, hasR⟩ = e ⟨b, hbsR⟩ := by
        apply Prod.ext _ hab
        apply Subtype.ext; exact ea.trans eb.symm
      have := e.injective this
      exact congrArg Subtype.val this
    have := Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
    simpa using this
  · intro o ho o' ho' hne hcap
    by_cases h : P o
    · obtain ⟨h1, _, h3, h4⟩ := hη1 o h
      rw [h1] at hcap
      have h5 : o' ∈ C (Classical.choose h) := (hC _ _).mpr ⟨ho', hcap⟩
      exact hne (Finset.card_le_one.mp (le_of_eq h3) _ h5 _ h4)
    · have h2 := (hη2G o h ho).2
      rw [Finset.card_eq_zero] at h2
      have h5 : o' ∈ C (η o) := (hC _ _).mpr ⟨ho', hcap⟩
      rw [h2] at h5; simp at h5

end LocalSearchFL.KMedian

open LocalSearchFL.KMedian


theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O : Finset Fa) (hcard : S.card = O.card) :
    ∃ η : Fa → Fa,
      (∀ o ∈ O, η o ∈ S) ∧
      (∀ s ∈ S, (∃ o₁ ∈ O, ∃ o₂ ∈ O, o₁ ≠ o₂ ∧ captures σS σO s o₁ ∧ captures σS σO s o₂) →
        ∀ o ∈ O, η o ≠ s) ∧
      (∀ s ∈ S, IsGood σS σO O s → (O.filter (fun o => η o = s)).card ≤ 2) ∧
      (∀ o ∈ O, ∀ o' ∈ O, o' ≠ o → ¬ captures σS σO (η o) o') := by
  exact sw4_core σS σO S O hcard
