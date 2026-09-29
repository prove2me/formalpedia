-- Prove2me | solution 1 for LocalSearchFL.KMedian.single_swap_locality_gap
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:50:55.991708+00:00
-- url     : https://prove2.me/submissions/9914e562-ac88-4a26-89ba-06fd9c0d5082

import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_kmCost



namespace LocalSearchFL.KMedian
end LocalSearchFL.KMedian

namespace LocalSearchFL.MultiSwap

/-- The **neighbourhood** `N_A(a)` of a facility `a` under an assignment `σ` of clients to
facilities (p. 548): the set of clients that `a` serves. -/
def nbhd {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa] (σ : Cl → Fa) (a : Fa) : Finset Cl :=
  Finset.univ.filter (fun j => σ j = a)

/-- The neighbourhood `N_A(T) = ⋃_{a ∈ T} N_A(a)` of a set `T` of facilities (p. 548): the set of
clients served by some facility of `T`. -/
def nbhdSet {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa] (σ : Cl → Fa) (T : Finset Fa) :
    Finset Cl :=
  Finset.univ.filter (fun j => σ j ∈ T)

/-- **Capture of a set** (§3.4, p. 551). Given the assignment `σS` of the clients to the
facilities of a solution `S` and the assignment `σO` to those of a solution `O`,
`capture(A) = {o ∈ O | |N_S(A) ∩ N_O(o)| > |N_O(o)|/2}`, stated in integers as
`|N_O(o)| < 2 |N_S(A) ∩ N_O(o)|`. -/
def capture {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (O A : Finset Fa) : Finset Fa :=
  O.filter (fun o => (nbhd σO o).card < 2 * (nbhdSet σS A ∩ nbhd σO o).card)

/-- A facility `s` is **good** (p. 549) if it captures no facility of `O`, i.e.
`capture({s}) = ∅`, and **bad** otherwise (Definition 3.1: `s` captures `o` iff
`|N_S(s) ∩ N_O(o)| > ½ |N_O(o)|`). -/
def IsGood {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (O : Finset Fa) (s : Fa) : Prop :=
  capture σS σO O {s} = ∅

end LocalSearchFL.MultiSwap
namespace LocalSearchFL.MultiSwap

/-- The **k-median cost** of a nonempty set `S` of open facilities (p. 548, §3):
`cost(S) = ∑_{j ∈ C} min_{i ∈ S} c_{ji}`, every client being served by its nearest open
facility. Only nonempty `S` have a cost. -/
noncomputable def kmCost {Cl Fa : Type} [Fintype Cl] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (S : Finset Fa) (hS : S.Nonempty) : ℝ :=
  ∑ j : Cl, S.inf' hS (fun i => I.c j i)

/-- **Local optimality for p-swaps** (p. 547 and §3.3, eq. (3), p. 551): `S` is locally optimum
for the neighbourhood `B(S) = {(S \ A) ∪ B | A ⊆ S, B ⊆ F, |A| = |B| ≤ p}`, i.e. no swap `⟨A, B⟩`
deleting a set `A ⊆ S` of at most `p` facilities and adding a set `B` of `|A|` facilities
decreases the cost. (`B` may meet `S`.) Whenever `S` is nonempty every such neighbour is
nonempty, so the quantifier over its nonemptiness proof `h` restricts nothing. -/
def IsPSwapLocalOpt {Cl Fa : Type} [Fintype Cl] [DecidableEq Fa] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (p : ℕ) (S : Finset Fa) (hS : S.Nonempty) : Prop :=
  ∀ A : Finset Fa, A ⊆ S → ∀ B : Finset Fa, A.card = B.card → A.card ≤ p →
    ∀ h : ((S \ A) ∪ B).Nonempty, kmCost I S hS ≤ kmCost I ((S \ A) ∪ B) h

end LocalSearchFL.MultiSwap
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

theorem pi_core {α β : Type} [DecidableEq β] (N : Finset α) (g : α → β) :
    ∃ π : Equiv.Perm α,
      (∀ j, π j ∈ N ↔ j ∈ N) ∧
      (∀ j, j ∉ N → π j = j) ∧
      ∀ j ∈ N, 2 * (N.filter (fun x => g x = g j)).card ≤ N.card → g (π j) ≠ g j := by
  classical
  set cs : List β := (N.image g).toList with hcs
  let key : α → ℕ := fun x => cs.idxOf (g x)
  let le : α → α → Bool := fun a b => decide (key a ≤ key b)
  set L := N.toList.mergeSort le with hL
  have hperm : L.Perm N.toList := List.mergeSort_perm _ _
  have hnd : L.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList N)
  have hmem : ∀ x, x ∈ L ↔ x ∈ N := fun x => by rw [hperm.mem_iff, Finset.mem_toList]
  have hsorted : L.Pairwise (fun a b => le a b = true) := List.pairwise_mergeSort (le := le) (fun a b c h1 h2 => show decide (key a ≤ key c) = true from
      decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2)))
    (fun a b => by
      rcases Nat.le_total (key a) (key b) with h | h
      · exact Bool.or_eq_true_iff.mpr (Or.inl (show decide (key a ≤ key b) = true from decide_eq_true h))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (show decide (key b ≤ key a) = true from decide_eq_true h))) N.toList
  have hlen : L.length = N.card := by rw [hperm.length_eq, Finset.length_toList]
  set n := L.length with hn
  have hsort' : ∀ a c (ha : a < n) (hc : c < n), a ≤ c → key L[a] ≤ key L[c] := by
    intro a c ha hc hac
    rcases Nat.lt_or_eq_of_le hac with h | h
    · have := List.pairwise_iff_getElem.mp hsorted a c ha hc h
      simpa [le] using this
    · subst h; exact le_rfl
  have hcsmem : ∀ x ∈ N, g x ∈ cs := fun x hx => by
    rw [hcs, Finset.mem_toList]; exact Finset.mem_image_of_mem g hx
  have hLN : ∀ m (hm : m < n), L[m] ∈ N := fun m hm => (hmem _).mp (List.getElem_mem hm)
  have hbetween : ∀ a m c (hc : c < n) (ham : a ≤ m) (hmc : m ≤ c),
      g (L[a]'(by omega)) = g L[c] →
      g (L[m]'(by omega)) = g (L[a]'(by omega)) := by
    intro a m c hc ham hmc hg
    have h1 := hsort' a m (by omega) (by omega) ham
    have h2 := hsort' m c (by omega) hc hmc
    have h3 : key L[a] = key L[c] := by simp only [key, hg]
    have h4 : key (L[m]'(by omega)) = key L[a] := by omega
    simp only [key] at h4
    exact (List.idxOf_inj (hcsmem _ (hLN _ _))).mp h4
  have hcount : ∀ a c (hc : c < n) (hac : a ≤ c), g (L[a]'(by omega)) = g L[c] →
      c + 1 - a ≤ (N.filter (fun x => g x = g (L[a]'(by omega)))).card := by
    intro a c hc hac hg
    let f : ℕ → α := fun m => L.getD m (L[a]'(by omega))
    have hsub : (Finset.Icc a c).image f ⊆ N.filter (fun x => g x = g (L[a]'(by omega))) := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_Icc] at hm
      have hmn : m < n := by omega
      simp only [f, List.getD_eq_getElem _ _ hmn, Finset.mem_filter]
      exact ⟨hLN _ _, hbetween a m c hc hm.1 hm.2 hg⟩
    have hinj : Set.InjOn f (Finset.Icc a c) := by
      intro m1 hm1 m2 hm2 he
      simp only [Finset.coe_Icc, Set.mem_Icc] at hm1 hm2
      simp only [f, List.getD_eq_getElem _ _ (show m1 < n by omega),
        List.getD_eq_getElem _ _ (show m2 < n by omega)] at he
      exact (hnd.getElem_inj_iff).mp he
    have := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injOn hinj, Nat.card_Icc] at this
  refine ⟨L.formPerm ^ (n / 2), ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ N
    · simp only [hj, iff_true]
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((hmem j).mpr hj)
      rw [List.formPerm_pow_apply_getElem _ hnd]
      exact hLN _ _
    · rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
        (List.formPerm_apply_of_notMem (fun h => hj ((hmem j).mp h))) _]
  · intro j hj
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self
        (List.formPerm_apply_of_notMem (fun h => hj ((hmem j).mp h))) _
  · intro j hj hcard heq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((hmem j).mpr hj)
    rw [List.formPerm_pow_apply_getElem _ hnd] at heq
    rw [← hlen] at hcard
    obtain ⟨k, hk, hkg, hkeq⟩ : ∃ k, ∃ hk : k < n, g L[k] = g L[i] ∧ k = (i + n / 2) % n :=
      ⟨(i + n / 2) % n, Nat.mod_lt _ (by omega), heq, rfl⟩
    by_cases hlt : i + n / 2 < n
    · rw [Nat.mod_eq_of_lt hlt] at hkeq
      have := hcount i k hk (by omega) hkg.symm
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hkeq
      have := hcount k i hi (by omega) hkg
      simp only [hkg] at this
      omega

theorem gap_core {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (p : ℕ) (hp : 1 ≤ p)
    (k : ℕ) (S : Finset Fa) (hS : S.Nonempty) (hSk : S.card = k)
    (hloc : IsPSwapLocalOpt I p S hS)
    (O : Finset Fa) (hO : O.Nonempty) (hOk : O.card ≤ k) :
    kmCost I S hS ≤ (3 + 2 / (p : ℝ)) * kmCost I O hO := by
  classical
  -- pad O to a set O' of size k
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
    (s := S \ O) (n := k - O.card) (by
      have h1 := Finset.card_sdiff_add_card_inter S O
      have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := O))
      omega)
  set O' := O ∪ T with hO'
  have hOO' : O ⊆ O' := Finset.subset_union_left
  have hO'card : S.card = O'.card := by
    rw [hO', Finset.card_union_of_disjoint]
    · omega
    · exact Finset.disjoint_of_subset_right hTsub Finset.disjoint_sdiff
  have hO'ne : O'.Nonempty := hO.mono hOO'
  have hcostO' : kmCost I O' hO'ne ≤ kmCost I O hO := by
    unfold kmCost
    apply Finset.sum_le_sum
    intro j _
    exact Finset.le_inf' _ _ (fun o ho => Finset.inf'_le _ (hOO' ho))
  -- nearest assignments
  have hexS : ∀ j, ∃ s ∈ S, ∀ s' ∈ S, I.c j s ≤ I.c j s' :=
    fun j => Finset.exists_min_image S (I.c j) hS
  have hexO : ∀ j, ∃ o ∈ O', ∀ o' ∈ O', I.c j o ≤ I.c j o' :=
    fun j => Finset.exists_min_image O' (I.c j) hO'ne
  choose σS hσS hσSmin using hexS
  choose σO hσO hσOmin using hexO
  have hkS : kmCost I S hS = ∑ j, I.c j (σS j) := by
    unfold kmCost
    apply Finset.sum_congr rfl
    intro j _
    exact le_antisymm (Finset.inf'_le _ (hσS j)) (Finset.le_inf' _ _ (hσSmin j))
  have hkO : kmCost I O' hO'ne = ∑ j, I.c j (σO j) := by
    unfold kmCost
    apply Finset.sum_congr rfl
    intro j _
    exact le_antisymm (Finset.inf'_le _ (hσO j)) (Finset.le_inf' _ _ (hσOmin j))
  -- weighted swaps
  obtain ⟨W, w, hW1, hWo, hWs, hWcap, hWde⟩ := ws_core σS σO S O' hO'card p hp
  -- labelling of clients by the deleted set containing their facility
  let g : Cl → Finset Fa := fun j =>
    if h : ∃ AB ∈ W, σS j ∈ AB.1 then (Classical.choose h).1 else ∅
  have hg : ∀ AB ∈ W, ∀ j, σS j ∈ AB.1 → g j = AB.1 := by
    intro AB hAB j hj
    have h : ∃ AB ∈ W, σS j ∈ AB.1 := ⟨AB, hAB, hj⟩
    simp only [g, dif_pos h]
    obtain ⟨h1, h2⟩ := Classical.choose_spec h
    rcases hWde _ h1 AB hAB with e | e
    · exact e
    · exact absurd hj (Finset.disjoint_left.mp e h2)
  have hg' : ∀ j, g j ≠ ∅ → σS j ∈ g j := by
    intro j hne
    by_cases h : ∃ AB ∈ W, σS j ∈ AB.1
    · simp only [g, dif_pos h]
      exact (Classical.choose_spec h).2
    · simp only [g, dif_neg h] at hne ⊢
      exact absurd rfl hne
  -- the permutations of Property 3.2
  have hπex : ∀ o : Fa, ∃ π : Equiv.Perm Cl,
      (∀ j, π j ∈ nbhd σO o ↔ j ∈ nbhd σO o) ∧ (∀ j, j ∉ nbhd σO o → π j = j) ∧
      ∀ j ∈ nbhd σO o, 2 * ((nbhd σO o).filter (fun x => g x = g j)).card ≤
        (nbhd σO o).card → g (π j) ≠ g j := fun o => pi_core _ g
  choose πo hπmem hπfix hπcl using hπex
  let π : Cl → Cl := fun j => πo (σO j) j
  have hmemN : ∀ j, j ∈ nbhd σO (σO j) := by
    intro j; simp [nbhd]
  have hπσ : ∀ j, σO (π j) = σO j := by
    intro j
    have := (hπmem (σO j) j).mpr (hmemN j)
    simpa [nbhd] using this
  have hπsum : ∀ F : Cl → ℝ, ∑ j, F (π j) = ∑ j, F j := by
    intro F
    rw [← Finset.sum_fiberwise Finset.univ σO (fun j => F (π j)),
      ← Finset.sum_fiberwise Finset.univ σO F]
    apply Finset.sum_congr rfl
    intro o _
    have e : ∀ j ∈ Finset.univ.filter (fun j => σO j = o), F (π j) = F (πo o j) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      simp only [π, hj.2]
    rw [Finset.sum_congr rfl e]
    apply Equiv.Perm.sum_comp
    intro j hj
    by_contra hn
    exact hj (hπfix o j hn)
  have hπA : ∀ AB ∈ W, ∀ j, σS j ∈ AB.1 → σO j ∉ AB.2 → σS (π j) ∉ AB.1 := by
    intro AB hAB j hj ho hπj
    set o := σO j with ho_def
    have hnc : o ∉ capture σS σO O' AB.1 := fun h => ho (hWcap AB hAB h)
    simp only [capture, Finset.mem_filter, not_and, not_lt] at hnc
    have hle := hnc (hσO j)
    have hsub : (nbhd σO o).filter (fun x => g x = g j) ⊆ nbhdSet σS AB.1 ∩ nbhd σO o := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_inter]
      refine ⟨?_, hx.1⟩
      simp only [nbhdSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hgj : g j = AB.1 := hg AB hAB j hj
      have hne : g x ≠ ∅ := by
        rw [hx.2, hgj]; intro h; rw [h] at hj; simp at hj
      have := hg' x hne
      rwa [hx.2, hgj] at this
    have hcl := hπcl o j (hmemN j)
      (le_trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)) hle)
    exact hcl (by rw [hg AB hAB _ hπj, hg AB hAB j hj])
  -- costs
  set Sj : Cl → ℝ := fun j => I.c j (σS j) with hSj
  set Oj : Cl → ℝ := fun j => I.c j (σO j) with hOj
  set Tj : Cl → ℝ := fun j => Oj j + Oj (π j) + Sj (π j) - Sj j with hTj
  have htri : ∀ j, I.c j (σS (π j)) ≤ Oj j + Oj (π j) + Sj (π j) := by
    intro j
    simp only [hOj, hSj, LocalSearchFL.Shared.MetricInstance.c]
    have h1 := I.triangle (Sum.inl j) (Sum.inr (σO j)) (Sum.inr (σS (π j)))
    have h2 := I.triangle (Sum.inr (σO j)) (Sum.inl (π j)) (Sum.inr (σS (π j)))
    have h3 := I.symm (Sum.inr (σO j)) (Sum.inl (π j))
    rw [← hπσ j] at h1 h2 h3 ⊢
    linarith
  have hT0 : ∀ j, 0 ≤ Tj j := by
    intro j
    have := hσSmin j (σS (π j)) (hσS _)
    have := htri j
    simp only [hTj, hSj] at *
    linarith
  have hswap : ∀ AB ∈ W, 0 ≤ ∑ j, ((if σO j ∈ AB.2 then Oj j - Sj j else 0) +
      (if σS j ∈ AB.1 then Tj j else 0)) := by
    intro AB hAB
    obtain ⟨hA, hB, hcardAB, hle, -⟩ := hW1 AB hAB
    let τ : Cl → Fa := fun j => if σO j ∈ AB.2 then σO j else
      if σS j ∈ AB.1 then σS (π j) else σS j
    have hτ : ∀ j, τ j ∈ (S \ AB.1) ∪ AB.2 := by
      intro j
      simp only [τ]
      split_ifs with h1 h2
      · exact Finset.mem_union_right _ h1
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hσS _, hπA AB hAB j h2 h1⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hσS _, h2⟩)
    have hne : ((S \ AB.1) ∪ AB.2).Nonempty := by
      by_cases h : (S \ AB.1).Nonempty
      · exact h.mono Finset.subset_union_left
      · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
        have e : AB.1 = S := Finset.Subset.antisymm hA h
        have : 0 < AB.2.card := by rw [← hcardAB, e]; exact Finset.card_pos.mpr hS
        exact (Finset.card_pos.mp this).mono Finset.subset_union_right
    have h1 := hloc AB.1 hA AB.2 hcardAB hle hne
    have h2 : kmCost I ((S \ AB.1) ∪ AB.2) hne ≤ ∑ j, I.c j (τ j) := by
      unfold kmCost
      exact Finset.sum_le_sum (fun j _ => Finset.inf'_le _ (hτ j))
    have h3 : ∀ j, I.c j (τ j) - Sj j ≤ (if σO j ∈ AB.2 then Oj j - Sj j else 0) +
        (if σS j ∈ AB.1 then Tj j else 0) := by
      intro j
      have := hT0 j
      have := htri j
      simp only [τ]
      split_ifs <;> simp only [hTj, hOj, hSj] at * <;> linarith
    have h4 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h3 j)
    rw [Finset.sum_sub_distrib] at h4
    rw [hkS] at h1
    simp only [hSj] at h4 ⊢
    linarith
  set q : ℝ := ((p : ℝ) + 1) / p with hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  -- sum over W with weights
  have hmain : 0 ≤ ∑ j, ((Oj j - Sj j) + q * Tj j) := by
    have h0 : 0 ≤ ∑ AB ∈ W, w AB * ∑ j, ((if σO j ∈ AB.2 then Oj j - Sj j else 0) +
        (if σS j ∈ AB.1 then Tj j else 0)) :=
      Finset.sum_nonneg (fun AB hAB => mul_nonneg (hW1 AB hAB).2.2.2.2.le (hswap AB hAB))
    have hcomm : ∑ AB ∈ W, w AB * ∑ j, ((if σO j ∈ AB.2 then Oj j - Sj j else 0) +
        (if σS j ∈ AB.1 then Tj j else 0)) = ∑ j, ∑ AB ∈ W, w AB *
        ((if σO j ∈ AB.2 then Oj j - Sj j else 0) + (if σS j ∈ AB.1 then Tj j else 0)) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    rw [hcomm] at h0
    refine h0.trans (Finset.sum_le_sum (fun j _ => ?_))
    · have e1 : ∑ AB ∈ W, w AB * ((if σO j ∈ AB.2 then Oj j - Sj j else 0) +
          (if σS j ∈ AB.1 then Tj j else 0)) =
          (Oj j - Sj j) * ∑ AB ∈ W.filter (fun AB => σO j ∈ AB.2), w AB +
          Tj j * ∑ AB ∈ W.filter (fun AB => σS j ∈ AB.1), w AB := by
        rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro AB _
        split_ifs <;> ring
      rw [e1, hWo _ (hσO j)]
      have := hWs _ (hσS j)
      have := hT0 j
      nlinarith
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hmain
  have hTsum : ∑ j, Tj j = 2 * ∑ j, Oj j := by
    simp only [hTj]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hπsum Oj, hπsum Sj]
    ring
  rw [hTsum] at hmain
  have hO'0 : 0 ≤ kmCost I O' hO'ne := by
    rw [hkO]; exact Finset.sum_nonneg (fun j _ => I.nonneg _ _)
  have hcoef : (3 + 2 / (p : ℝ)) = 1 + 2 * q := by
    rw [hq]; field_simp; ring
  rw [hkS]
  calc ∑ j, I.c j (σS j) ≤ (1 + 2 * q) * kmCost I O' hO'ne := by
        rw [hkO]; simp only [hSj, hOj] at hmain; nlinarith
    _ ≤ (3 + 2 / (p : ℝ)) * kmCost I O hO := by
        rw [hcoef]
        have : 0 ≤ q := by rw [hq]; positivity
        nlinarith

end LocalSearchFL.MultiSwap

namespace LocalSearchFL.KMedian

theorem km_eq {Cl Fa : Type} [Fintype Cl] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (S : Finset Fa) (hS : S.Nonempty) :
    kmCost I S hS = LocalSearchFL.MultiSwap.kmCost I S hS := rfl

theorem km_anti {Cl Fa : Type} [Fintype Cl] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (T U : Finset Fa) (hT : T.Nonempty) (hU : U.Nonempty) (h : T ⊆ U) :
    kmCost I U hU ≤ kmCost I T hT := by
  unfold kmCost
  apply Finset.sum_le_sum
  intro j _
  exact Finset.le_inf' _ _ (fun o ho => Finset.inf'_le _ (h ho))

theorem km_congr {Cl Fa : Type} [Fintype Cl] (I : LocalSearchFL.Shared.MetricInstance Cl Fa)
    (T U : Finset Fa) (hT : T.Nonempty) (hU : U.Nonempty) (h : T = U) :
    kmCost I T hT = kmCost I U hU := by subst h; rfl

theorem swap_to_pswap {Cl Fa : Type} [Fintype Cl] [DecidableEq Fa]
    (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (S : Finset Fa) (hS : S.Nonempty)
    (hloc : IsSwapLocalOpt I S hS) : LocalSearchFL.MultiSwap.IsPSwapLocalOpt I 1 S hS := by
  intro A hA B hAB hA1 h
  rw [← km_eq, ← km_eq]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hA1 with h0 | h1
  · have hA0 : A = ∅ := Finset.card_eq_zero.mp h0
    have hB0 : B = ∅ := Finset.card_eq_zero.mp (hAB ▸ h0)
    subst hA0 hB0
    exact le_of_eq (km_congr I _ _ _ _ (by simp))
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp (hAB ▸ h1)
    have ha : a ∈ S := hA (Finset.mem_singleton_self a)
    by_cases hb : b ∈ S
    · apply km_anti
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_sdiff.mp hx).1
      · rw [Finset.mem_singleton.mp hx]; exact hb
    · refine le_trans (hloc a ha b hb) (le_of_eq (km_congr I _ _ _ _ ?_))
      ext x; simp [Finset.mem_sdiff, Finset.mem_erase, or_comm, and_comm]

theorem gap5_core {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (k : ℕ) (S : Finset Fa) (hS : S.Nonempty) (hSk : S.card = k)
    (hloc : IsSwapLocalOpt I S hS)
    (O : Finset Fa) (hO : O.Nonempty) (hOk : O.card ≤ k) :
    kmCost I S hS ≤ 5 * kmCost I O hO := by
  have := LocalSearchFL.MultiSwap.gap_core I 1 le_rfl k S hS hSk (swap_to_pswap I S hS hloc) O hO hOk
  rw [km_eq, km_eq]
  norm_num at this ⊢
  exact this

end LocalSearchFL.KMedian

open LocalSearchFL.KMedian


theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl]
    [Fintype Fa] [DecidableEq Fa]
    (I : LocalSearchFL.Shared.MetricInstance Cl Fa) (k : ℕ) (S : Finset Fa) (hS : S.Nonempty) (hSk : S.card = k)
    (hloc : IsSwapLocalOpt I S hS)
    (O : Finset Fa) (hO : O.Nonempty) (hOk : O.card ≤ k) :
    kmCost I S hS ≤ 5 * kmCost I O hO := by
  exact gap5_core I k S hS hSk hloc O hO hOk
