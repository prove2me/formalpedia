-- Prove2me | solution 1 for LocalSearchFL.MultiSwap.exists_partition_claim_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:09:48.087027+00:00
-- url     : https://prove2.me/submissions/055c8580-2291-4085-bf09-d931bd27a2f5

import Mathlib
import Definitions.Def_LocalSearchFL_MultiSwap_capture



namespace LocalSearchFL.MultiSwap

section
variable {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
  (σS σO : Cl → Fa) (O : Finset Fa)

theorem cap_mono {X Y : Finset Fa} (h : X ⊆ Y) :
    capture σS σO O X ⊆ capture σS σO O Y := by
  intro o ho
  simp only [capture, Finset.mem_filter] at ho ⊢
  refine ⟨ho.1, lt_of_lt_of_le ho.2 ?_⟩
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  apply Finset.inter_subset_inter_right
  intro j hj
  simp only [nbhdSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact h hj

theorem cap_disj {X Y : Finset Fa} (h : Disjoint X Y) :
    Disjoint (capture σS σO O X) (capture σS σO O Y) := by
  rw [Finset.disjoint_left]
  intro o hx hy
  simp only [capture, Finset.mem_filter] at hx hy
  have hd : Disjoint (nbhdSet σS X ∩ nbhd σO o) (nbhdSet σS Y ∩ nbhd σO o) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [nbhdSet, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact Finset.disjoint_left.mp h h1.1 h2.1
  have := Finset.card_union_of_disjoint hd
  have hsub : (nbhdSet σS X ∩ nbhd σO o) ∪ (nbhdSet σS Y ∩ nbhd σO o) ⊆ nbhd σO o := by
    intro j hj
    rcases Finset.mem_union.mp hj with h | h <;> exact (Finset.mem_inter.mp h).2
  have := Finset.card_le_card hsub
  omega

theorem cap_sub (X : Finset Fa) : capture σS σO O X ⊆ O := Finset.filter_subset _ _

theorem ivt_aux (D : Finset Fa) : ∀ A0 : Finset Fa,
    A0.card ≤ (capture σS σO O A0).card →
    (capture σS σO O (A0 ∪ D)).card ≤ (A0 ∪ D).card →
    ∃ A, A0 ⊆ A ∧ A ⊆ A0 ∪ D ∧ (capture σS σO O A).card = A.card := by
  induction D using Finset.induction_on with
  | empty =>
    intro A0 h1 h2
    simp only [Finset.union_empty] at h2
    exact ⟨A0, le_rfl, Finset.subset_union_left, le_antisymm h2 h1⟩
  | insert x D hx ih =>
    intro A0 h1 h2
    by_cases he : (capture σS σO O A0).card = A0.card
    · exact ⟨A0, le_rfl, Finset.subset_union_left, he⟩
    · have h3 : (insert x A0).card ≤ (capture σS σO O (insert x A0)).card := by
        have := Finset.card_insert_le x A0
        have := Finset.card_le_card (cap_mono σS σO O (Finset.subset_insert x A0))
        omega
      have e : insert x A0 ∪ D = A0 ∪ insert x D := by
        ext y; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      rw [← e] at h2
      obtain ⟨A, hA1, hA2, hA3⟩ := ih (insert x A0) h3 h2
      exact ⟨A, (Finset.subset_insert x A0).trans hA1, e ▸ hA2, hA3⟩

open Classical in
theorem exists_block (T O' : Finset Fa) (hcapT : capture σS σO O T ⊆ O')
    (hcard : T.card = O'.card) (hbad : ∃ b ∈ T, ¬ IsGood σS σO O b) :
    ∃ b ∈ T, ¬ IsGood σS σO O b ∧ ∃ A, b ∈ A ∧ A ⊆ insert b (T.filter (IsGood σS σO O)) ∧
      (capture σS σO O A).card = A.card := by
  classical
  set G := T.filter (IsGood σS σO O) with hG
  have key : ∃ b ∈ T, ¬ IsGood σS σO O b ∧ ((capture σS σO O {b}).card ≤ 1 ∨
      (capture σS σO O (insert b G)).card ≤ G.card + 1) := by
    by_contra hcon
    push_neg at hcon
    set Bd := T.filter (fun s => ¬ IsGood σS σO O s) with hBd
    obtain ⟨b0, hb0T, hb0⟩ := hbad
    have hb0B : b0 ∈ Bd := Finset.mem_filter.mpr ⟨hb0T, hb0⟩
    set F := (Bd.erase b0).biUnion (fun b => capture σS σO O {b}) with hF
    have hFcard : F.card = ∑ b ∈ Bd.erase b0, (capture σS σO O {b}).card := by
      apply Finset.card_biUnion
      intro b _ b' _ hbb'
      exact cap_disj σS σO O (Finset.disjoint_singleton.mpr hbb')
    have hFge : 2 * (Bd.erase b0).card ≤ F.card := by
      rw [hFcard, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro b hb
      have hb' := Finset.mem_filter.mp (Finset.mem_of_mem_erase hb)
      exact (hcon b hb'.1 hb'.2).1
    have hdisj : Disjoint F (capture σS σO O (insert b0 G)) := by
      rw [hF, Finset.disjoint_biUnion_left]
      intro b hb
      apply cap_disj
      rw [Finset.disjoint_singleton_left, Finset.mem_insert, not_or]
      have hb' := Finset.mem_filter.mp (Finset.mem_of_mem_erase hb)
      exact ⟨Finset.ne_of_mem_erase hb, fun h => hb'.2 (Finset.mem_filter.mp h).2⟩
    have hsub : F ∪ capture σS σO O (insert b0 G) ⊆ O' := by
      apply Finset.union_subset
      · rw [hF, Finset.biUnion_subset]
        intro b hb
        refine (cap_mono σS σO O ?_).trans hcapT
        rw [Finset.singleton_subset_iff]
        exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hb)).1
      · refine (cap_mono σS σO O ?_).trans hcapT
        exact Finset.insert_subset hb0T (Finset.filter_subset _ _)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at h1
    have h2 := (hcon b0 hb0T hb0).2
    have h3 : G.card + Bd.card = T.card := Finset.card_filter_add_card_filter_not _
    have h4 := Finset.card_erase_of_mem hb0B
    have h5 := Finset.card_pos.mpr ⟨b0, hb0B⟩
    omega
  obtain ⟨b, hbT, hb, hcase⟩ := key
  have hge : ({b} : Finset Fa).card ≤ (capture σS σO O {b}).card := by
    rw [Finset.card_singleton, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
    exact hb
  refine ⟨b, hbT, hb, ?_⟩
  rcases hcase with h | h
  · obtain ⟨A, h1, h2, h3⟩ := ivt_aux σS σO O ∅ {b} hge (by simpa using h)
    refine ⟨A, h1 (Finset.mem_singleton_self b), ?_, h3⟩
    rw [Finset.union_empty] at h2
    exact h2.trans (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
  · have e : ({b} : Finset Fa) ∪ G = insert b G := by rw [Finset.insert_eq]
    have h' : (capture σS σO O ({b} ∪ G)).card ≤ ({b} ∪ G).card := by
      rw [e]
      have : b ∉ G := fun h => hb (Finset.mem_filter.mp h).2
      rw [Finset.card_insert_of_notMem this]
      exact h
    obtain ⟨A, h1, h2, h3⟩ := ivt_aux σS σO O G {b} hge h'
    exact ⟨A, h1 (Finset.mem_singleton_self b), e ▸ h2, h3⟩

theorem part_rec : ∀ n (T O' : Finset Fa), T.card = n → capture σS σO O T ⊆ O' →
    T.card = O'.card →
    ∃ (L : List (Finset Fa × Finset Fa)) (Ar Br : Finset Fa),
      (∀ ab ∈ L, ab.1 ⊆ T ∧ ab.2 ⊆ O' ∧ ab.1.card = ab.2.card ∧
        ab.2 = capture σS σO O ab.1 ∧
        (∃ b ∈ ab.1, ¬ IsGood σS σO O b ∧ ∀ s ∈ ab.1, s ≠ b → IsGood σS σO O s)) ∧
      L.Pairwise (fun x y => Disjoint x.1 y.1 ∧ Disjoint x.2 y.2) ∧
      Ar ⊆ T ∧ Br ⊆ O' ∧ (∀ ab ∈ L, Disjoint ab.1 Ar ∧ Disjoint ab.2 Br) ∧
      (∀ s ∈ T, (∃ ab ∈ L, s ∈ ab.1) ∨ s ∈ Ar) ∧
      (∀ o ∈ O', (∃ ab ∈ L, o ∈ ab.2) ∨ o ∈ Br) ∧
      Ar.card = Br.card ∧ ∀ s ∈ Ar, IsGood σS σO O s := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T O' hn hcapT hcard
  by_cases hbad : ∃ b ∈ T, ¬ IsGood σS σO O b
  · obtain ⟨b, hbT, hb, A, hbA, hAsub, hAcard⟩ := exists_block σS σO O T O' hcapT hcard hbad
    have hAT : A ⊆ T := hAsub.trans (Finset.insert_subset hbT (Finset.filter_subset _ _))
    have hcapA : capture σS σO O A ⊆ O' := (cap_mono σS σO O hAT).trans hcapT
    have hT'card : (T \ A).card = T.card - A.card := Finset.card_sdiff_of_subset hAT
    have hO'card : (O' \ capture σS σO O A).card = O'.card - (capture σS σO O A).card :=
      Finset.card_sdiff_of_subset hcapA
    have hApos : 0 < A.card := Finset.card_pos.mpr ⟨b, hbA⟩
    have hAle : A.card ≤ T.card := Finset.card_le_card hAT
    have hlt : (T \ A).card < n := by omega
    have hcap' : capture σS σO O (T \ A) ⊆ O' \ capture σS σO O A := by
      intro o ho
      rw [Finset.mem_sdiff]
      refine ⟨hcapT (cap_mono σS σO O Finset.sdiff_subset ho), fun h => ?_⟩
      exact Finset.disjoint_left.mp (cap_disj σS σO O Finset.sdiff_disjoint) ho h
    obtain ⟨L, Ar, Br, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      ih _ hlt (T \ A) (O' \ capture σS σO O A) rfl hcap' (by omega)
    refine ⟨(A, capture σS σO O A) :: L, Ar, Br, ?_, ?_, h3.trans Finset.sdiff_subset,
      h4.trans Finset.sdiff_subset, ?_, ?_, ?_, h8, h9⟩
    · intro ab hab
      rcases List.mem_cons.mp hab with rfl | hab
      · refine ⟨hAT, hcapA, hAcard.symm, rfl, b, hbA, hb, ?_⟩
        intro s hs hsb
        have := hAsub hs
        rw [Finset.mem_insert] at this
        rcases this with h | h
        · exact absurd h hsb
        · exact (Finset.mem_filter.mp h).2
      · obtain ⟨a1, a2, a3, a4, a5⟩ := h1 ab hab
        exact ⟨a1.trans Finset.sdiff_subset, a2.trans Finset.sdiff_subset, a3, a4, a5⟩
    · refine List.Pairwise.cons ?_ h2
      intro y hy
      obtain ⟨a1, a2, -⟩ := h1 y hy
      exact ⟨Finset.disjoint_of_subset_right a1 Finset.disjoint_sdiff,
        Finset.disjoint_of_subset_right a2 Finset.disjoint_sdiff⟩
    · intro ab hab
      rcases List.mem_cons.mp hab with rfl | hab
      · exact ⟨Finset.disjoint_of_subset_right h3 Finset.disjoint_sdiff,
          Finset.disjoint_of_subset_right h4 Finset.disjoint_sdiff⟩
      · exact h5 ab hab
    · intro s hs
      by_cases hsA : s ∈ A
      · exact Or.inl ⟨_, List.mem_cons_self, hsA⟩
      · rcases h6 s (Finset.mem_sdiff.mpr ⟨hs, hsA⟩) with ⟨ab, hab, h⟩ | h
        · exact Or.inl ⟨ab, List.mem_cons_of_mem _ hab, h⟩
        · exact Or.inr h
    · intro o ho
      by_cases hoA : o ∈ capture σS σO O A
      · exact Or.inl ⟨_, List.mem_cons_self, hoA⟩
      · rcases h7 o (Finset.mem_sdiff.mpr ⟨ho, hoA⟩) with ⟨ab, hab, h⟩ | h
        · exact Or.inl ⟨ab, List.mem_cons_of_mem _ hab, h⟩
        · exact Or.inr h
  · push_neg at hbad
    refine ⟨[], T, O', by simp, List.Pairwise.nil, le_rfl, le_rfl, by simp,
      fun s hs => Or.inr hs, fun o ho => Or.inr ho, hcard, hbad⟩

end

theorem partition_core {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O : Finset Fa) (hcard : S.card = O.card) :
    ∃ (m : ℕ) (A B : Fin m → Finset Fa) (Ar Br : Finset Fa),
      (∀ i, A i ⊆ S) ∧ Ar ⊆ S ∧ (∀ s ∈ S, (∃ i, s ∈ A i) ∨ s ∈ Ar) ∧
      (∀ i i', i ≠ i' → Disjoint (A i) (A i')) ∧ (∀ i, Disjoint (A i) Ar) ∧
      (∀ i, B i ⊆ O) ∧ Br ⊆ O ∧ (∀ o ∈ O, (∃ i, o ∈ B i) ∨ o ∈ Br) ∧
      (∀ i i', i ≠ i' → Disjoint (B i) (B i')) ∧ (∀ i, Disjoint (B i) Br) ∧
      (∀ i, (A i).card = (B i).card ∧ B i = capture σS σO O (A i)) ∧ Ar.card = Br.card ∧
      (∀ i, ∃ b ∈ A i, ¬ IsGood σS σO O b ∧ ∀ s ∈ A i, s ≠ b → IsGood σS σO O s) ∧
      (∀ s ∈ Ar, IsGood σS σO O s) := by
  obtain ⟨L, Ar, Br, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    part_rec σS σO O _ S O rfl (cap_sub σS σO O S) hcard
  have hmem : ∀ i : Fin L.length, L.get i ∈ L := fun i => List.get_mem L i
  have hpw : ∀ i i' : Fin L.length, i ≠ i' →
      Disjoint (L.get i).1 (L.get i').1 ∧ Disjoint (L.get i).2 (L.get i').2 := by
    intro i i' hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact List.pairwise_iff_getElem.mp h2 i i' i.2 i'.2 h
    · have := List.pairwise_iff_getElem.mp h2 i' i i'.2 i.2 h
      exact ⟨this.1.symm, this.2.symm⟩
  refine ⟨L.length, fun i => (L.get i).1, fun i => (L.get i).2, Ar, Br,
    fun i => (h1 _ (hmem i)).1, h3, ?_, fun i i' h => (hpw i i' h).1,
    fun i => (h5 _ (hmem i)).1, fun i => (h1 _ (hmem i)).2.1, h4, ?_,
    fun i i' h => (hpw i i' h).2, fun i => (h5 _ (hmem i)).2,
    fun i => ⟨(h1 _ (hmem i)).2.2.1, (h1 _ (hmem i)).2.2.2.1⟩, h8,
    fun i => (h1 _ (hmem i)).2.2.2.2, h9⟩
  · intro s hs
    rcases h6 s hs with ⟨ab, hab, h⟩ | h
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hab
      exact Or.inl ⟨i, h⟩
    · exact Or.inr h
  · intro o ho
    rcases h7 o ho with ⟨ab, hab, h⟩ | h
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hab
      exact Or.inl ⟨i, h⟩
    · exact Or.inr h

end LocalSearchFL.MultiSwap

open LocalSearchFL.MultiSwap


theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O : Finset Fa) (hcard : S.card = O.card) :
    ∃ (m : ℕ) (A B : Fin m → Finset Fa) (Ar Br : Finset Fa),
      -- `A_1, …, A_{r-1}, A_r` partition `S`
      (∀ i, A i ⊆ S) ∧ Ar ⊆ S ∧ (∀ s ∈ S, (∃ i, s ∈ A i) ∨ s ∈ Ar) ∧
      (∀ i i', i ≠ i' → Disjoint (A i) (A i')) ∧ (∀ i, Disjoint (A i) Ar) ∧
      -- `B_1, …, B_{r-1}, B_r` partition `O`
      (∀ i, B i ⊆ O) ∧ Br ⊆ O ∧ (∀ o ∈ O, (∃ i, o ∈ B i) ∨ o ∈ Br) ∧
      (∀ i i', i ≠ i' → Disjoint (B i) (B i')) ∧ (∀ i, Disjoint (B i) Br) ∧
      -- property 1
      (∀ i, (A i).card = (B i).card ∧ B i = capture σS σO O (A i)) ∧ Ar.card = Br.card ∧
      -- property 2
      (∀ i, ∃ b ∈ A i, ¬ IsGood σS σO O b ∧ ∀ s ∈ A i, s ≠ b → IsGood σS σO O s) ∧
      -- property 3
      (∀ s ∈ Ar, IsGood σS σO O s) := by
  exact partition_core σS σO S O hcard
