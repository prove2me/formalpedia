-- Prove2me | solution 1 for LocalSearchFL.MultiSwap.exists_weighted_swaps
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:15:23.803+00:00
-- url     : https://prove2.me/submissions/56e8e505-30fb-415d-8e24-c32c4d2e3b0f

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

theorem ws_core {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O : Finset Fa) (hcard : S.card = O.card) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (W : Finset (Finset Fa × Finset Fa)) (w : Finset Fa × Finset Fa → ℝ),
      (∀ AB ∈ W, AB.1 ⊆ S ∧ AB.2 ⊆ O ∧ AB.1.card = AB.2.card ∧ AB.1.card ≤ p ∧ 0 < w AB) ∧
      (∀ o ∈ O, ∑ AB ∈ W.filter (fun AB => o ∈ AB.2), w AB = 1) ∧
      (∀ s ∈ S, ∑ AB ∈ W.filter (fun AB => s ∈ AB.1), w AB ≤ ((p : ℝ) + 1) / p) ∧
      (∀ AB ∈ W, capture σS σO O AB.1 ⊆ AB.2) ∧
      (∀ AB ∈ W, ∀ AB' ∈ W, AB.1 = AB'.1 ∨ Disjoint AB.1 AB'.1) := by
  classical
  obtain ⟨m, A, B, Ar, Br, hAS, hArS, hScov, hAdisj, hAAr, hBO, hBrO, hOcov, hBdisj, hBBr,
    hcapeq, hArBr, hbad, hArgood⟩ := partition_core σS σO S O hcard
  set q : ℝ := ((p : ℝ) + 1) / p with hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ hp0]; linarith
  set Gr : Option (Fin m) → Finset Fa := fun j => j.elim Ar
    (fun i => if p < (A i).card then (A i).filter (IsGood σS σO O) else ∅) with hGr
  set Cr : Option (Fin m) → Finset Fa := fun j => j.elim Br
    (fun i => if p < (A i).card then B i else ∅) with hCr
  have hGrA : ∀ i, Gr (some i) ⊆ A i := by
    intro i; simp only [hGr, Option.elim_some]
    split_ifs
    · exact Finset.filter_subset _ _
    · exact Finset.empty_subset _
  have hGrS : ∀ j, Gr j ⊆ S := by
    intro j; cases j with
    | none => exact hArS
    | some i => exact (hGrA i).trans (hAS i)
  have hGrgood : ∀ j, ∀ g ∈ Gr j, IsGood σS σO O g := by
    intro j g hg; cases j with
    | none => exact hArgood g hg
    | some i =>
      simp only [hGr, Option.elim_some] at hg
      split_ifs at hg
      · exact (Finset.mem_filter.mp hg).2
      · simp at hg
  have hCrO : ∀ j, Cr j ⊆ O := by
    intro j; cases j with
    | none => exact hBrO
    | some i =>
      simp only [hCr, Option.elim_some]
      split_ifs
      · exact hBO i
      · exact Finset.empty_subset _
  have hGrdisj : ∀ j j', j ≠ j' → Disjoint (Gr j) (Gr j') := by
    intro j j' hne
    cases j with
    | none =>
      cases j' with
      | none => exact absurd rfl hne
      | some i' => exact Finset.disjoint_of_subset_right (hGrA i') (hAAr i').symm
    | some i =>
      cases j' with
      | none => exact Finset.disjoint_of_subset_left (hGrA i) (hAAr i)
      | some i' =>
        have : i ≠ i' := fun h => hne (by rw [h])
        exact Finset.disjoint_of_subset_left (hGrA i)
          (Finset.disjoint_of_subset_right (hGrA i') (hAdisj i i' this))
  -- card of good part of a block
  have hgoodcard : ∀ i, ((A i).filter (IsGood σS σO O)).card + 1 = (A i).card := by
    intro i
    obtain ⟨b, hb, hbg, hrest⟩ := hbad i
    have h1 := Finset.card_filter_add_card_filter_not (s := A i) (IsGood σS σO O)
    have h2 : (A i).filter (fun s => ¬ IsGood σS σO O s) = {b} := by
      ext s; simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hs, hsg⟩; by_contra hsb; exact hsg (hrest s hs hsb)
      · rintro rfl; exact ⟨hb, hbg⟩
    rw [h2, Finset.card_singleton] at h1
    exact h1
  have hratio : ∀ j, (Gr j).Nonempty → ((Cr j).card : ℝ) / (Gr j).card ≤ q := by
    intro j hne
    have hpos : (0 : ℝ) < (Gr j).card := by exact_mod_cast Finset.card_pos.mpr hne
    rw [div_le_iff₀ hpos]
    cases j with
    | none =>
      simp only [hGr, hCr, Option.elim_none] at hpos ⊢
      rw [← hArBr]; nlinarith
    | some i =>
      simp only [hGr, hCr, Option.elim_some] at hpos ⊢
      split_ifs with hlt
      · rw [if_pos hlt] at hpos
        have h1 := hgoodcard i
        have h2 := (hcapeq i).1
        have h3 : ((A i).filter (IsGood σS σO O)).card = (B i).card - 1 := by omega
        have h4 : ((B i).card : ℝ) = ((A i).filter (IsGood σS σO O)).card + 1 := by
          rw [h3]; push_cast [show 1 ≤ (B i).card by omega]; ring
        rw [h4, hq, div_mul_eq_mul_div, le_div_iff₀ hp0]
        have h5 : (p : ℝ) ≤ ((A i).filter (IsGood σS σO O)).card := by
          exact_mod_cast (show p ≤ ((A i).filter (IsGood σS σO O)).card by omega)
        nlinarith
      · simp
  have hCrGr : ∀ j, (Cr j).Nonempty → (Gr j).Nonempty := by
    intro j hne
    cases j with
    | none =>
      simp only [hGr, hCr, Option.elim_none] at hne ⊢
      rw [← Finset.card_pos, hArBr]; exact Finset.card_pos.mpr hne
    | some i =>
      simp only [hGr, hCr, Option.elim_some] at hne ⊢
      split_ifs with hlt
      · rw [← Finset.card_pos]; have := hgoodcard i; omega
      · rw [if_neg hlt] at hne; simp at hne
  -- the swaps
  set W1 : Finset (Finset Fa × Finset Fa) :=
    (Finset.univ.filter (fun i => (A i).card ≤ p)).image (fun i => (A i, B i)) with hW1
  set W2 : Finset (Finset Fa × Finset Fa) := Finset.univ.biUnion
    (fun j => (Gr j ×ˢ Cr j).image (fun x => (({x.1} : Finset Fa), ({x.2} : Finset Fa))))
    with hW2
  set w : Finset Fa × Finset Fa → ℝ := fun AB =>
    if ∃ g ∈ AB.1, ¬ IsGood σS σO O g then 1 else
      ∑ j, ∑ g ∈ AB.1, if g ∈ Gr j then 1 / ((Gr j).card : ℝ) else 0 with hw
  have hw1 : ∀ i, w (A i, B i) = 1 := by
    intro i
    obtain ⟨b, hb, hbg, -⟩ := hbad i
    simp only [hw]
    rw [if_pos ⟨b, hb, hbg⟩]
  have hw2 : ∀ j, ∀ g ∈ Gr j, ∀ o, w ({g}, {o}) = 1 / ((Gr j).card : ℝ) := by
    intro j g hg o
    simp only [hw]
    rw [if_neg (by
      rintro ⟨g', hg', hbad'⟩
      rw [Finset.mem_singleton] at hg'
      exact hbad' (hg' ▸ hGrgood j g hg))]
    simp only [Finset.sum_singleton]
    rw [Finset.sum_eq_single j]
    · rw [if_pos hg]
    · intro j' _ hj'
      rw [if_neg]
      intro hg'
      exact Finset.disjoint_left.mp (hGrdisj j' j hj') hg' hg
    · intro h; exact absurd (Finset.mem_univ j) h
  have hAne : ∀ i, (A i).Nonempty := fun i => by
    obtain ⟨b, hb, -⟩ := hbad i; exact ⟨b, hb⟩
  have hAinj : ∀ i i', A i = A i' → i = i' := by
    intro i i' h
    by_contra hne
    have := hAdisj i i' hne
    rw [h, disjoint_self, Finset.bot_eq_empty] at this
    exact (hAne i').ne_empty this
  have hdisjW : Disjoint W1 W2 := by
    rw [Finset.disjoint_left]
    intro AB h1 h2
    simp only [hW1, hW2, Finset.mem_image, Finset.mem_biUnion, Finset.mem_product,
      Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨i, -, rfl⟩ := h1
    obtain ⟨j, ⟨g, o⟩, ⟨hg, -⟩, he⟩ := h2
    obtain ⟨b, hb, hbg, -⟩ := hbad i
    have : ({g} : Finset Fa) = A i := (Prod.ext_iff.mp he).1
    rw [← this, Finset.mem_singleton] at hb
    exact hbg (hb ▸ hGrgood j g hg)
  have hsumW : ∀ F : Finset Fa × Finset Fa → ℝ, ∑ AB ∈ W1 ∪ W2, F AB =
      ∑ i ∈ Finset.univ.filter (fun i => (A i).card ≤ p), F (A i, B i) +
      ∑ j, ∑ x ∈ Gr j ×ˢ Cr j, F ({x.1}, {x.2}) := by
    intro F
    rw [Finset.sum_union hdisjW, hW1, Finset.sum_image, hW2, Finset.sum_biUnion]
    · congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_image]
      intro x _ y _ hxy
      simp only [Prod.ext_iff, Finset.singleton_inj] at hxy
      exact Prod.ext hxy.1 hxy.2
    · intro j _ j' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro AB h1 h2
      simp only [Finset.mem_image, Finset.mem_product] at h1 h2
      obtain ⟨⟨g, o⟩, ⟨hg, -⟩, rfl⟩ := h1
      obtain ⟨⟨g', o'⟩, ⟨hg', -⟩, he⟩ := h2
      simp only [Prod.ext_iff, Finset.singleton_inj] at he
      rw [he.1] at hg'
      exact Finset.disjoint_left.mp (hGrdisj j j' hne) hg hg'
    · intro i _ i' _ h
      exact hAinj i i' (Prod.ext_iff.mp h).1
  refine ⟨W1 ∪ W2, w, ?_, ?_, ?_, ?_, ?_⟩
  · intro AB hAB
    rcases Finset.mem_union.mp hAB with h | h
    · simp only [hW1, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
      obtain ⟨i, hi, rfl⟩ := h
      refine ⟨hAS i, hBO i, (hcapeq i).1, hi, ?_⟩
      rw [hw1]; exact one_pos
    · simp only [hW2, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_product] at h
      obtain ⟨j, ⟨g, o⟩, ⟨hg, ho⟩, rfl⟩ := h
      refine ⟨Finset.singleton_subset_iff.mpr (hGrS j hg),
        Finset.singleton_subset_iff.mpr (hCrO j ho), by simp, by simpa using hp, ?_⟩
      rw [hw2 j g hg]
      have : (0 : ℝ) < (Gr j).card := by exact_mod_cast Finset.card_pos.mpr ⟨g, hg⟩
      positivity
  · intro o ho
    rw [Finset.sum_filter, hsumW]
    have e2 : ∀ j, ∑ x ∈ Gr j ×ˢ Cr j,
        (if o ∈ (({x.1} : Finset Fa), ({x.2} : Finset Fa)).2 then
          w (({x.1} : Finset Fa), ({x.2} : Finset Fa)) else 0) =
        if o ∈ Cr j then 1 else 0 := by
      intro j
      rw [Finset.sum_product]
      have : ∀ g ∈ Gr j, ∑ o' ∈ Cr j, (if o ∈ (({g} : Finset Fa), ({o'} : Finset Fa)).2 then
          w (({g} : Finset Fa), ({o'} : Finset Fa)) else 0) =
          if o ∈ Cr j then 1 / ((Gr j).card : ℝ) else 0 := by
        intro g hg
        simp only [Finset.mem_singleton]
        rw [Finset.sum_ite_eq]
        split_ifs
        · rw [hw2 j g hg]
        · rfl
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      split_ifs with hoc
      · have : (0 : ℝ) < (Gr j).card := by
          exact_mod_cast Finset.card_pos.mpr (hCrGr j ⟨o, hoc⟩)
        field_simp
      · simp
    rw [Finset.sum_congr rfl (fun j _ => e2 j), Fintype.sum_option, Finset.sum_filter]
    have e3 : ∀ i : Fin m, ((if (A i).card ≤ p then
        (if o ∈ (A i, B i).2 then w (A i, B i) else 0) else 0) +
        if o ∈ Cr (some i) then (1 : ℝ) else 0) = if o ∈ B i then 1 else 0 := by
      intro i
      simp only [hCr, Option.elim_some, hw1]
      by_cases h : (A i).card ≤ p
      · have h' : ¬ p < (A i).card := by omega
        simp only [h, h', if_true, if_false]; simp
      · have h' : p < (A i).card := by omega
        simp only [h, h', if_true, if_false]; simp
    have e4 : ∑ i : Fin m, (if (A i).card ≤ p then
        (if o ∈ (A i, B i).2 then w (A i, B i) else 0) else 0) +
        ((if o ∈ Cr none then (1 : ℝ) else 0) + ∑ i : Fin m, if o ∈ Cr (some i) then 1 else 0) =
        (if o ∈ Br then (1 : ℝ) else 0) + ∑ i : Fin m, if o ∈ B i then 1 else 0 := by
      rw [← Finset.sum_congr rfl (fun i _ => e3 i), Finset.sum_add_distrib]
      simp only [hCr, Option.elim_none]
      ring
    rw [e4]
    rcases hOcov o ho with ⟨i0, hi0⟩ | hbr
    · rw [if_neg (Finset.disjoint_left.mp (hBBr i0) hi0), Finset.sum_eq_single i0]
      · rw [if_pos hi0]; ring
      · intro i _ hne
        rw [if_neg]
        intro h
        exact Finset.disjoint_left.mp (hBdisj i i0 hne) h hi0
      · intro h; exact absurd (Finset.mem_univ i0) h
    · rw [if_pos hbr, Finset.sum_eq_zero]
      · ring
      · intro i _
        rw [if_neg]
        intro h
        exact Finset.disjoint_left.mp (hBBr i) h hbr
  · intro s hs
    rw [Finset.sum_filter, hsumW]
    have e2 : ∀ j, ∑ x ∈ Gr j ×ˢ Cr j,
        (if s ∈ (({x.1} : Finset Fa), ({x.2} : Finset Fa)).1 then
          w (({x.1} : Finset Fa), ({x.2} : Finset Fa)) else 0) ≤
        if s ∈ Gr j then q else 0 := by
      intro j
      rw [Finset.sum_product]
      have : ∀ g ∈ Gr j, ∑ o' ∈ Cr j, (if s ∈ (({g} : Finset Fa), ({o'} : Finset Fa)).1 then
          w (({g} : Finset Fa), ({o'} : Finset Fa)) else 0) =
          if s = g then ((Cr j).card : ℝ) / (Gr j).card else 0 := by
        intro g hg
        simp only [Finset.mem_singleton]
        split_ifs
        · rw [Finset.sum_congr rfl (fun o' _ => hw2 j g hg o'), Finset.sum_const, nsmul_eq_mul]
          ring
        · simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
      split_ifs with h
      · exact hratio j ⟨s, h⟩
      · exact le_rfl
    refine le_trans (add_le_add le_rfl (Finset.sum_le_sum (fun j _ => e2 j))) ?_
    rw [Fintype.sum_option, Finset.sum_filter]
    have e3 : ∀ i : Fin m, ((if (A i).card ≤ p then
        (if s ∈ (A i, B i).1 then w (A i, B i) else 0) else 0) +
        if s ∈ Gr (some i) then q else 0) ≤ if s ∈ A i then q else 0 := by
      intro i
      simp only [hGr, Option.elim_some, hw1]
      by_cases h : (A i).card ≤ p
      · have h' : ¬ p < (A i).card := by omega
        simp only [h, h', if_true, if_false]
        split_ifs <;> simp only [Finset.notMem_empty] at * <;> linarith
      · have h' : p < (A i).card := by omega
        simp only [h, h', if_true, if_false]
        have hq0 : 0 ≤ q := by linarith
        split_ifs <;> first | linarith |
          exact absurd (Finset.mem_filter.mp ‹s ∈ Finset.filter _ _›).1 ‹s ∉ A i›
    have e4 : ∑ i : Fin m, (if (A i).card ≤ p then
        (if s ∈ (A i, B i).1 then w (A i, B i) else 0) else 0) +
        ((if s ∈ Gr none then q else 0) + ∑ i : Fin m, if s ∈ Gr (some i) then q else 0) ≤
        (if s ∈ Ar then q else 0) + ∑ i : Fin m, if s ∈ A i then q else 0 := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => e3 i)
      rw [Finset.sum_add_distrib] at this
      simp only [hGr, Option.elim_none] at this ⊢
      linarith
    refine le_trans e4 ?_
    rcases hScov s hs with ⟨i0, hi0⟩ | har
    · rw [if_neg (Finset.disjoint_left.mp (hAAr i0) hi0), Finset.sum_eq_single i0]
      · rw [if_pos hi0]; simp
      · intro i _ hne
        rw [if_neg]
        intro h
        exact Finset.disjoint_left.mp (hAdisj i i0 hne) h hi0
      · intro h; exact absurd (Finset.mem_univ i0) h
    · rw [if_pos har, Finset.sum_eq_zero]
      · simp
      · intro i _
        rw [if_neg]
        intro h
        exact Finset.disjoint_left.mp (hAAr i) h har
  · intro AB hAB
    rcases Finset.mem_union.mp hAB with h | h
    · simp only [hW1, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
      obtain ⟨i, -, rfl⟩ := h
      rw [(hcapeq i).2]
    · simp only [hW2, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_product] at h
      obtain ⟨j, ⟨g, o⟩, ⟨hg, -⟩, rfl⟩ := h
      have := hGrgood j g hg
      simp only [IsGood] at this
      simp only [this, Finset.empty_subset]
  · intro AB hAB AB' hAB'
    rcases Finset.mem_union.mp hAB with h | h <;> rcases Finset.mem_union.mp hAB' with h' | h'
    · simp only [hW1, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h h'
      obtain ⟨i, -, rfl⟩ := h
      obtain ⟨i', -, rfl⟩ := h'
      by_cases hii : i = i'
      · left; rw [hii]
      · right; exact hAdisj i i' hii
    · simp only [hW1, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
      simp only [hW2, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_product] at h'
      obtain ⟨i, hi, rfl⟩ := h
      obtain ⟨j, ⟨g, o⟩, ⟨hg, -⟩, rfl⟩ := h'
      right
      rcases j with _ | i'
      · exact Finset.disjoint_of_subset_right (Finset.singleton_subset_iff.mpr hg) (hAAr i)
      · 
        have hne : i ≠ i' := by
          rintro rfl
          simp only [hGr, Option.elim_some] at hg
          rw [if_neg (by omega)] at hg
          simp at hg
        exact Finset.disjoint_of_subset_right
          (Finset.singleton_subset_iff.mpr (hGrA i' hg)) (hAdisj i i' hne)
    · simp only [hW1, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h'
      simp only [hW2, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_product] at h
      obtain ⟨i, hi, rfl⟩ := h'
      obtain ⟨j, ⟨g, o⟩, ⟨hg, -⟩, rfl⟩ := h
      right
      rcases j with _ | i'
      · exact (Finset.disjoint_of_subset_right (Finset.singleton_subset_iff.mpr hg) (hAAr i)).symm
      · 
        have hne : i ≠ i' := by
          rintro rfl
          simp only [hGr, Option.elim_some] at hg
          rw [if_neg (by omega)] at hg
          simp at hg
        exact (Finset.disjoint_of_subset_right
          (Finset.singleton_subset_iff.mpr (hGrA i' hg)) (hAdisj i i' hne)).symm
    · simp only [hW2, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_product] at h h'
      obtain ⟨j, ⟨g, o⟩, -, rfl⟩ := h
      obtain ⟨j', ⟨g', o'⟩, -, rfl⟩ := h'
      by_cases hgg : g = g'
      · left; simp [hgg]
      · right; simpa using hgg

end LocalSearchFL.MultiSwap

open LocalSearchFL.MultiSwap


theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O : Finset Fa) (hcard : S.card = O.card) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (W : Finset (Finset Fa × Finset Fa)) (w : Finset Fa × Finset Fa → ℝ),
      (∀ AB ∈ W, AB.1 ⊆ S ∧ AB.2 ⊆ O ∧ AB.1.card = AB.2.card ∧ AB.1.card ≤ p ∧ 0 < w AB) ∧
      (∀ o ∈ O, ∑ AB ∈ W.filter (fun AB => o ∈ AB.2), w AB = 1) ∧
      (∀ s ∈ S, ∑ AB ∈ W.filter (fun AB => s ∈ AB.1), w AB ≤ ((p : ℝ) + 1) / p) ∧
      (∀ AB ∈ W, capture σS σO O AB.1 ⊆ AB.2) ∧
      (∀ AB ∈ W, ∀ AB' ∈ W, AB.1 = AB'.1 ∨ Disjoint AB.1 AB'.1) := by
  exact ws_core σS σO S O hcard p hp
