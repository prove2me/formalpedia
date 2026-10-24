-- Prove2me | solution 1 for LeeSviridenkoVondrak.LocalSearch.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:55:34.183924+00:00
-- url     : https://prove2.me/submissions/ee68272e-9b5f-4eee-9c87-82c1d58804cc

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Model
open scoped symmDiff

namespace LSV95

open Finset

variable {E : Type} [DecidableEq E]

/-- Rado's theorem (hard direction) for an integer-valued monotone submodular function
bounded by cardinality. -/
theorem rado {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : Finset E → ℤ)
    (hmono : ∀ S T, S ⊆ T → ρ S ≤ ρ T)
    (hsub : ∀ S T, ρ (S ∪ T) + ρ (S ∩ T) ≤ ρ S + ρ T)
    (hcard : ∀ S, ρ S ≤ S.card) :
    ∀ (N : ℕ) (S : ι → Finset E), ∑ j, (S j).card ≤ N →
      (∀ K : Finset ι, (K.card : ℤ) ≤ ρ (K.biUnion S)) →
      ∃ f : ι → E, Function.Injective f ∧ (∀ j, f j ∈ S j) ∧
        ρ (univ.image f) = Fintype.card ι := by
  intro N
  induction N with
  | zero =>
    intro S hS H
    by_cases hι : IsEmpty ι
    · have hu : (univ : Finset ι) = ∅ := Finset.univ_eq_empty
      refine ⟨fun j => (hι.false j).elim, fun a => (hι.false a).elim,
        fun j => (hι.false j).elim, ?_⟩
      rw [hu, Finset.image_empty, Fintype.card_eq_zero]
      have h1 := H ∅
      have h4 := hcard ∅
      simp at h1 h4
      push_cast; linarith
    · exfalso
      rw [not_isEmpty_iff] at hι
      obtain ⟨j⟩ := hι
      have h1 := H {j}
      rw [Finset.card_singleton, Finset.singleton_biUnion] at h1
      have hz : (S j).card = 0 := by
        have := Finset.single_le_sum (f := fun j => (S j).card) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
        omega
      rw [Finset.card_eq_zero] at hz
      rw [hz] at h1
      have := hcard ∅
      simp at this h1; linarith
  | succ N ih =>
    intro S hS H
    by_cases hsmall : ∀ j, (S j).card ≤ 1
    · -- every set is a singleton
      have hone : ∀ j, (S j).card = 1 := by
        intro j
        have h1 := H {j}
        rw [Finset.card_singleton, Finset.singleton_biUnion] at h1
        have := hcard (S j)
        have := hsmall j
        omega
      choose f hf using fun j => Finset.card_eq_one.1 (hone j)
      have hfm : ∀ j, f j ∈ S j := fun j => by rw [hf j]; simp
      have hinj : Function.Injective f := by
        intro a b hab
        by_contra hne
        have h2 := H {a, b}
        rw [Finset.card_pair hne] at h2
        have : ({a, b} : Finset ι).biUnion S = {f a} := by
          ext x; simp [hf, hab]
        rw [this] at h2
        have := hcard {f a}
        simp at this h2; linarith
      refine ⟨f, hinj, hfm, le_antisymm ?_ ?_⟩
      · have := hcard (univ.image f)
        rw [Finset.card_image_of_injective _ hinj] at this
        simpa using this
      · have h := H univ
        have : univ.biUnion S = univ.image f := by
          ext x; simp [hf, eq_comm]
        rw [this] at h
        simpa using h
    · push Not at hsmall
      obtain ⟨j0, hj0⟩ := hsmall
      obtain ⟨x1, hx1, x2, hx2, hne⟩ := Finset.one_lt_card.1 hj0
      -- the two reduced families
      set S1 := Function.update S j0 ((S j0).erase x1) with hS1
      set S2 := Function.update S j0 ((S j0).erase x2) with hS2
      have hsum : ∀ x ∈ S j0, ∑ j, (Function.update S j0 ((S j0).erase x) j).card ≤ N := by
        intro x hx
        have e : ∀ T : ι → Finset E, ∑ j, (T j).card =
            (T j0).card + ∑ j ∈ univ.erase j0, (T j).card := by
          intro T; rw [Finset.add_sum_erase _ (fun j => (T j).card) (mem_univ j0)]
        rw [e] at hS ⊢
        simp only [Function.update_self]
        have : ∑ j ∈ univ.erase j0, (Function.update S j0 ((S j0).erase x) j).card =
            ∑ j ∈ univ.erase j0, (S j).card := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        rw [this, Finset.card_erase_of_mem hx]
        have : 1 ≤ (S j0).card := Finset.card_pos.2 ⟨x, hx⟩
        omega
      -- transversal of a reduced family is one of S
      have lift : ∀ x ∈ S j0, (∀ K : Finset ι, (K.card : ℤ) ≤
          ρ (K.biUnion (Function.update S j0 ((S j0).erase x)))) →
          ∃ f : ι → E, Function.Injective f ∧ (∀ j, f j ∈ S j) ∧
            ρ (univ.image f) = Fintype.card ι := by
        intro x hx HK
        obtain ⟨f, hinj, hm, hr⟩ := ih _ (hsum x hx) HK
        refine ⟨f, hinj, fun j => ?_, hr⟩
        have := hm j
        by_cases hj : j = j0
        · subst hj; simp at this; exact this.2
        · rwa [Function.update_of_ne hj] at this
      by_contra hcon
      have F1 : ∃ K : Finset ι, ρ (K.biUnion S1) < K.card := by
        by_contra h; push Not at h; exact hcon (lift x1 hx1 h)
      have F2 : ∃ K : Finset ι, ρ (K.biUnion S2) < K.card := by
        by_contra h; push Not at h; exact hcon (lift x2 hx2 h)
      obtain ⟨K1, hK1⟩ := F1
      obtain ⟨K2, hK2⟩ := F2
      -- j0 ∈ K1, K2
      have key : ∀ (x : E) (K : Finset ι), ρ (K.biUnion (Function.update S j0 ((S j0).erase x)))
          < K.card → j0 ∈ K ∧ ρ (((S j0).erase x) ∪ (K.erase j0).biUnion S) ≤ (K.erase j0).card := by
        intro x K hK
        have hj : j0 ∈ K := by
          by_contra hj
          have : K.biUnion (Function.update S j0 ((S j0).erase x)) = K.biUnion S := by
            apply Finset.biUnion_congr rfl
            intro j hjK
            rw [Function.update_of_ne]; rintro rfl; exact hj hjK
          rw [this] at hK
          linarith [H K]
        refine ⟨hj, ?_⟩
        have e : K.biUnion (Function.update S j0 ((S j0).erase x)) =
            ((S j0).erase x) ∪ (K.erase j0).biUnion S := by
          conv_lhs => rw [← Finset.insert_erase hj]
          rw [Finset.biUnion_insert, Function.update_self]
          congr 1
          apply Finset.biUnion_congr rfl
          intro j hjK
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hjK)]
        rw [e] at hK
        have : (K.card : ℤ) = (K.erase j0).card + 1 := by
          rw [Finset.card_erase_of_mem hj]
          have : 1 ≤ K.card := Finset.card_pos.2 ⟨j0, hj⟩
          omega
        linarith
      obtain ⟨_, h1⟩ := key x1 K1 hK1
      obtain ⟨_, h2⟩ := key x2 K2 hK2
      set L1 := K1.erase j0
      set L2 := K2.erase j0
      have hn1 : j0 ∉ L1 := Finset.notMem_erase j0 K1
      have hn2 : j0 ∉ L2 := Finset.notMem_erase j0 K2
      have hU := H (insert j0 (L1 ∪ L2))
      have hI := H (L1 ∩ L2)
      have hsm := hsub (((S j0).erase x1) ∪ L1.biUnion S) (((S j0).erase x2) ∪ L2.biUnion S)
      have m1 := hmono ((insert j0 (L1 ∪ L2)).biUnion S)
        ((((S j0).erase x1) ∪ L1.biUnion S) ∪ (((S j0).erase x2) ∪ L2.biUnion S)) (by
        intro y hy
        simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_union] at hy
        obtain ⟨j, hj, hy⟩ := hy
        simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_biUnion]
        rcases hj with rfl | hj | hj
        · by_cases h : y = x1
          · subst h; right; left; exact ⟨hne, hy⟩
          · left; left; exact ⟨h, hy⟩
        · left; right; exact ⟨j, hj, hy⟩
        · right; right; exact ⟨j, hj, hy⟩)
      have m2 := hmono ((L1 ∩ L2).biUnion S)
        ((((S j0).erase x1) ∪ L1.biUnion S) ∩ (((S j0).erase x2) ∪ L2.biUnion S)) (by
        intro y hy
        simp only [Finset.mem_biUnion, Finset.mem_inter] at hy
        obtain ⟨j, ⟨hj1, hj2⟩, hy⟩ := hy
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_biUnion]
        exact ⟨Or.inr ⟨j, hj1, hy⟩, Or.inr ⟨j, hj2, hy⟩⟩)
      have c1 : (insert j0 (L1 ∪ L2)).card = (L1 ∪ L2).card + 1 := by
        rw [Finset.card_insert_of_notMem]
        simp [hn1, hn2]
      have c2 := Finset.card_union_add_card_inter L1 L2
      rw [c1] at hU
      push_cast at hU
      have : ((L1 ∪ L2).card : ℤ) + (L1 ∩ L2).card = L1.card + L2.card := by exact_mod_cast c2
      linarith

end LSV95

namespace LSV95

open Finset

section rank
variable {α : Type} [DecidableEq α]

noncomputable def rk (M : Matroid α) (S : Finset α) : ℕ := (M.eRk (↑S : Set α)).toNat

lemma rk_cast (M : Matroid α) (S : Finset α) : ((rk M S : ℕ) : ℕ∞) = M.eRk (↑S : Set α) := by
  unfold rk
  apply ENat.natCast_toNat
  apply ne_top_of_lt
  exact (M.eRk_le_encard _).trans_lt (Set.Finite.encard_lt_top (Finset.finite_toSet S))

lemma rk_le_card (M : Matroid α) (S : Finset α) : rk M S ≤ S.card := by
  have h := M.eRk_le_encard (↑S : Set α)
  rw [← rk_cast, Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

lemma rk_mono (M : Matroid α) {S T : Finset α} (h : S ⊆ T) : rk M S ≤ rk M T := by
  have := M.eRk_mono (show (↑S : Set α) ⊆ ↑T from by exact_mod_cast h)
  rw [← rk_cast, ← rk_cast] at this
  exact_mod_cast this

lemma rk_submod (M : Matroid α) (S T : Finset α) :
    rk M (S ∪ T) + rk M (S ∩ T) ≤ rk M S + rk M T := by
  have := M.eRk_submod (↑S : Set α) ↑T
  rw [← Finset.coe_inter, ← Finset.coe_union, ← rk_cast, ← rk_cast, ← rk_cast, ← rk_cast] at this
  have h : ((rk M (S ∩ T) + rk M (S ∪ T) : ℕ) : ℕ∞) ≤ ((rk M S + rk M T : ℕ) : ℕ∞) := by
    push_cast; exact this
  have := (Nat.cast_le (α := ℕ∞)).1 h
  omega

lemma rk_of_indep (M : Matroid α) {S : Finset α} (h : M.Indep (↑S : Set α)) :
    rk M S = S.card := by
  have := h.eRk_eq_encard
  rw [← rk_cast, Set.encard_coe_eq_coe_finsetCard] at this
  exact_mod_cast this

lemma indep_of_rk (M : Matroid α) {S : Finset α} (h : S.card ≤ rk M S) :
    M.Indep (↑S : Set α) := by
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite (Finset.finite_toSet S), ← rk_cast,
    Set.encard_coe_eq_coe_finsetCard]
  have := rk_le_card M S
  have : rk M S = S.card := le_antisymm this h
  rw [this]

lemma rk_union_le (M : Matroid α) (S T : Finset α) : rk M (S ∪ T) ≤ rk M S + T.card := by
  have := rk_submod M S T
  have := rk_le_card M T
  omega

end rank

/-- The counting inequality: for `X` independent and a family `Is` of subsets of an independent
`I` covering every element at most `q` times, `∑ r(Is i ∪ X) ≥ ∑ |Is i| + (m-q)|X|`. -/
lemma count_ineq {n : ℕ} (M : Matroid (Fin n)) (I X : Finset (Fin n))
    (hI : M.Indep (↑I : Set (Fin n))) (hX : M.Indep (↑X : Set (Fin n))) (m q : ℕ) (hqm : q ≤ m)
    (Is : Fin m → Finset (Fin n)) (hIs : ∀ i, Is i ⊆ I)
    (hc : ∀ x ∈ I, (univ.filter (fun i => x ∈ Is i)).card ≤ q) :
    (((m - q : ℕ) : ℤ) * X.card + ∑ i, ((Is i).card : ℤ)) ≤ ∑ i, ((rk M (Is i ∪ X) : ℕ) : ℤ) := by
  classical
  obtain ⟨B', hB', hXB'⟩ := hX.subset_isBasis_of_subset
    (show (↑X : Set (Fin n)) ⊆ ↑(X ∪ I) from by exact_mod_cast Finset.subset_union_left)
  set I' := (I \ X).filter (fun a => a ∈ B') with hI'
  have hB'eq : (↑(X ∪ I') : Set (Fin n)) = B' := by
    ext b
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, hI', Finset.mem_filter,
      Finset.mem_sdiff]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact hXB' h
      · exact h
    · intro h
      have := hB'.subset h
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at this
      by_cases hb : b ∈ X
      · left; exact hb
      · right; exact ⟨⟨this.resolve_left hb, hb⟩, h⟩
  have hindep : M.Indep (↑(X ∪ I') : Set (Fin n)) := by rw [hB'eq]; exact hB'.indep
  have hdisj : Disjoint X I' := by
    rw [Finset.disjoint_left]; intro a ha ha'
    simp [hI'] at ha'; exact ha'.1.2 ha
  -- |I| ≤ |X| + |I'|
  have hII' : I.card ≤ X.card + I'.card := by
    have h1 : rk M (X ∪ I) = rk M (X ∪ I') := by
      have := hB'.eRk_eq_encard
      rw [← hB'eq, ← rk_cast, Set.encard_coe_eq_coe_finsetCard] at this
      rw [rk_of_indep M hindep]; exact_mod_cast this
    have h2 := rk_mono M (show I ⊆ X ∪ I from Finset.subset_union_right)
    rw [rk_of_indep M hI, h1, rk_of_indep M hindep, Finset.card_union_of_disjoint hdisj] at h2
    exact h2
  have hI'I : I' ⊆ I := fun a ha => by simp [hI'] at ha; exact ha.1.1
  -- each term
  have hterm : ∀ i, (Is i ∩ I').card + X.card ≤ rk M (Is i ∪ X) := by
    intro i
    have hsub : (Is i ∩ I') ∪ X ⊆ X ∪ I' := by
      intro a ha
      simp only [Finset.mem_union, Finset.mem_inter] at ha ⊢
      tauto
    have hind : M.Indep (↑((Is i ∩ I') ∪ X) : Set (Fin n)) :=
      hindep.subset (by exact_mod_cast hsub)
    have := rk_mono M (show (Is i ∩ I') ∪ X ⊆ Is i ∪ X from
      Finset.union_subset_union Finset.inter_subset_left le_rfl)
    rw [rk_of_indep M hind, Finset.card_union_of_disjoint] at this
    · exact this
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_right hdisj.symm
  -- double counting
  have hdc : ∑ i, (Is i \ I').card ≤ q * X.card := by
    have e : ∀ i, (Is i \ I').card = ∑ a ∈ I \ I', if a ∈ Is i then 1 else 0 := by
      intro i
      rw [← Finset.card_filter]
      congr 1
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨hIs i h1, h2⟩, h1⟩
      · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
    simp_rw [e]
    rw [Finset.sum_comm]
    have : ∀ a ∈ I \ I', (∑ i, if a ∈ Is i then 1 else 0) ≤ q := by
      intro a ha
      rw [← Finset.card_filter]
      exact hc a (Finset.mem_sdiff.1 ha).1
    calc (∑ a ∈ I \ I', ∑ i, if a ∈ Is i then 1 else 0) ≤ ∑ a ∈ I \ I', q :=
          Finset.sum_le_sum this
      _ = (I \ I').card * q := by simp
      _ ≤ X.card * q := by
          apply Nat.mul_le_mul_right
          rw [Finset.card_sdiff_of_subset hI'I]; omega
      _ = q * X.card := by ring
  have hsplit : ∀ i, (Is i).card = (Is i ∩ I').card + (Is i \ I').card := by
    intro i; rw [add_comm, Finset.card_sdiff_add_card_inter]
  have hsum : ∑ i, ((Is i).card : ℤ) + ((m : ℤ) * X.card) ≤
      ∑ i, ((rk M (Is i ∪ X) : ℕ) : ℤ) + ∑ i, ((Is i \ I').card : ℤ) := by
    have : ∀ i, ((Is i).card : ℤ) + X.card ≤ ((rk M (Is i ∪ X) : ℕ) : ℤ) + (Is i \ I').card := by
      intro i
      have := hterm i
      have := hsplit i
      have h : (Is i).card + X.card ≤ rk M (Is i ∪ X) + (Is i \ I').card := by omega
      exact_mod_cast h
    have := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin m))) => this i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using this
  have hdc' : ∑ i, ((Is i \ I').card : ℤ) ≤ (q : ℤ) * X.card := by exact_mod_cast hdc
  have : ((m - q : ℕ) : ℤ) = (m : ℤ) - q := by push_cast [Nat.cast_sub hqm]; ring
  rw [this]
  nlinarith

end LSV95

namespace LSV95

open Finset

/-- slice of a set of pairs at the second coordinate `i`. -/
def sl {n m : ℕ} (T : Finset (Fin n × Fin m)) (i : Fin m) : Finset (Fin n) :=
  univ.filter (fun x => (x, i) ∈ T)

lemma mem_sl {n m : ℕ} (T : Finset (Fin n × Fin m)) (i : Fin m) (x : Fin n) :
    x ∈ sl T i ↔ (x, i) ∈ T := by simp [sl]

lemma card_eq_sum_sl {n m : ℕ} (T : Finset (Fin n × Fin m)) :
    T.card = ∑ i, (sl T i).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := univ) (fun _ _ => mem_univ _)]
  apply Finset.sum_congr rfl
  intro i _
  have : T.filter (fun p => p.2 = i) = (sl T i).image (fun x => (x, i)) := by
    ext ⟨x, j⟩
    simp only [Finset.mem_filter, Finset.mem_image, mem_sl]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨x, h, rfl⟩
    · rintro ⟨y, h, hy⟩
      simp only [Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy; exact ⟨h, rfl⟩
  rw [this, Finset.card_image_of_injective]
  intro a b h; simpa using h

theorem core {n : ℕ} (M : Matroid (Fin n)) (I J : Finset (Fin n))
    (hI : M.Indep (↑I : Set (Fin n))) (hJ : M.Indep (↑J : Set (Fin n))) (m q : ℕ) (hqm : q ≤ m)
    (Is : Fin m → Finset (Fin n)) (hIs : ∀ i, Is i ⊆ I)
    (hc : ∀ x ∈ I, (univ.filter (fun i => x ∈ Is i)).card ≤ q) :
    ∃ C : Fin m → Finset (Fin n), (∀ i, C i ⊆ J) ∧
      (∀ x ∈ J, (univ.filter (fun i => x ∈ C i)).card = m - q) ∧
      ∀ i, M.Indep (↑(Is i ∪ C i) : Set (Fin n)) := by
  classical
  let ι := {p : Fin n × Fin (m - q) // p.1 ∈ J}
  let S : ι → Finset (Fin n × Fin m) := fun p => univ.image (fun i => (p.1.1, i))
  let ρ : Finset (Fin n × Fin m) → ℤ := fun T =>
    ∑ i, (((rk M (Is i ∪ sl T i) : ℕ) : ℤ) - (Is i).card)
  have hmono : ∀ S T, S ⊆ T → ρ S ≤ ρ T := by
    intro S T h
    apply Finset.sum_le_sum
    intro i _
    have : sl S i ⊆ sl T i := fun x hx => by rw [mem_sl] at hx ⊢; exact h hx
    have := rk_mono M (Finset.union_subset_union (le_refl (Is i)) this)
    have : ((rk M (Is i ∪ sl S i) : ℕ) : ℤ) ≤ rk M (Is i ∪ sl T i) := by exact_mod_cast this
    linarith
  have hsub : ∀ S T, ρ (S ∪ T) + ρ (S ∩ T) ≤ ρ S + ρ T := by
    intro S T
    simp only [ρ]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have e1 : Is i ∪ sl (S ∪ T) i = (Is i ∪ sl S i) ∪ (Is i ∪ sl T i) := by
      ext x; simp only [Finset.mem_union, mem_sl]; tauto
    have e2 : Is i ∪ sl (S ∩ T) i = (Is i ∪ sl S i) ∩ (Is i ∪ sl T i) := by
      ext x; simp only [Finset.mem_union, Finset.mem_inter, mem_sl]; tauto
    have := rk_submod M (Is i ∪ sl S i) (Is i ∪ sl T i)
    rw [← e1, ← e2] at this
    have : ((rk M (Is i ∪ sl (S ∪ T) i) : ℕ) : ℤ) + rk M (Is i ∪ sl (S ∩ T) i) ≤
      rk M (Is i ∪ sl S i) + rk M (Is i ∪ sl T i) := by exact_mod_cast this
    linarith
  have hterm : ∀ T i, ((rk M (Is i ∪ sl T i) : ℕ) : ℤ) - (Is i).card ≤ (sl T i).card := by
    intro T i
    have h1 := rk_union_le M (Is i) (sl T i)
    have h2 : M.Indep (↑(Is i) : Set (Fin n)) := hI.subset (by exact_mod_cast hIs i)
    rw [rk_of_indep M h2] at h1
    have : ((rk M (Is i ∪ sl T i) : ℕ) : ℤ) ≤ (Is i).card + (sl T i).card := by exact_mod_cast h1
    linarith
  have hcard : ∀ T, ρ T ≤ T.card := by
    intro T
    rw [card_eq_sum_sl T]; push_cast
    exact Finset.sum_le_sum (fun i _ => hterm T i)
  have hH : ∀ K : Finset ι, (K.card : ℤ) ≤ ρ (K.biUnion S) := by
    intro K
    set X := K.image (fun p => p.1.1) with hXdef
    have hXJ : X ⊆ J := by
      intro x hx; simp only [hXdef, Finset.mem_image] at hx
      obtain ⟨p, _, rfl⟩ := hx; exact p.2
    have hsl : ∀ i, sl (K.biUnion S) i = X := by
      intro i; ext x
      simp only [mem_sl, Finset.mem_biUnion, S, Finset.mem_image, Finset.mem_univ, true_and,
        Prod.mk.injEq, hXdef]
      constructor
      · rintro ⟨p, hp, j, h1, _⟩; exact ⟨p, hp, h1⟩
      · rintro ⟨p, hp, h1⟩; exact ⟨p, hp, i, h1, rfl⟩
    have hci := count_ineq M I X hI (hJ.subset (by exact_mod_cast hXJ)) m q hqm Is hIs hc
    have hK : K.card ≤ X.card * (m - q) := by
      have : K.card ≤ (X ×ˢ (univ : Finset (Fin (m - q)))).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.1)
        · intro p hp
          simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hXdef, Finset.mem_image,
            Finset.coe_univ, Set.mem_univ, and_true]
          exact ⟨p, hp, rfl⟩
        · intro a _ b _ h; exact Subtype.ext h
      simpa using this
    simp only [ρ, hsl]
    rw [Finset.sum_sub_distrib]
    have : (K.card : ℤ) ≤ ((m - q : ℕ) : ℤ) * X.card := by
      have : (K.card : ℤ) ≤ (X.card : ℤ) * ((m - q : ℕ) : ℤ) := by exact_mod_cast hK
      linarith
    linarith
  obtain ⟨f, hinj, hfS, hρ⟩ := rado ρ hmono hsub hcard _ S le_rfl hH
  have hfst : ∀ p, (f p).1 = p.1.1 := by
    intro p
    have := hfS p
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at this
    obtain ⟨i, hi⟩ := this; rw [← hi]
  let C : Fin m → Finset (Fin n) := fun i => sl (univ.image f) i
  refine ⟨C, ?_, ?_, ?_⟩
  · intro i x hx
    simp only [C, mem_sl, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨p, hp⟩ := hx
    have := hfst p
    rw [hp] at this; simp only at this; rw [this]; exact p.2
  · intro x hx
    have : univ.filter (fun i => x ∈ C i) =
        univ.image (fun t : Fin (m - q) => (f ⟨(x, t), hx⟩).2) := by
      ext i
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, mem_sl, Finset.mem_image]
      constructor
      · rintro ⟨p, hp⟩
        have h1 := hfst p
        rw [hp] at h1
        refine ⟨p.1.2, ?_⟩
        have : p = ⟨(x, p.1.2), hx⟩ := by
          apply Subtype.ext; apply Prod.ext
          · exact h1.symm
          · rfl
        rw [← this, hp]
      · rintro ⟨t, ht⟩
        refine ⟨⟨(x, t), hx⟩, ?_⟩
        apply Prod.ext
        · exact hfst _
        · exact ht
    rw [this, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro t1 t2 h
    have h' : f ⟨(x, t1), hx⟩ = f ⟨(x, t2), hx⟩ := by
      apply Prod.ext
      · rw [hfst, hfst]
      · exact h
    have := hinj h'
    have := congrArg (fun p : ι => p.1.2) this
    exact this
  · -- every term is tight
    have htot : ρ (univ.image f) = ∑ i, ((sl (univ.image f) i).card : ℤ) := by
      rw [hρ]
      have := card_eq_sum_sl (univ.image f)
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ] at this
      exact_mod_cast this
    have heq := (Finset.sum_eq_sum_iff_of_le
      (fun i (_ : i ∈ (univ : Finset (Fin m))) => hterm (univ.image f) i)).1 htot
    intro i
    have h := heq i (mem_univ i)
    apply indep_of_rk
    have h2 := Finset.card_union_le (Is i) (C i)
    have : ((Is i).card : ℤ) + (C i).card ≤ rk M (Is i ∪ C i) := by
      simp only [C]; linarith
    have : (Is i).card + (C i).card ≤ rk M (Is i ∪ C i) := by exact_mod_cast this
    omega

end LSV95

open LeeSviridenkoVondrak.LocalSearch in
theorem solution {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (A B : Finset (Fin n)) (hA : M.IsBase (↑A : Set (Fin n)))
    (hB : M.IsBase (↑B : Set (Fin n))) (m q : ℕ) (As : Fin m → Finset (Fin n))
    (hAs : ∀ i, As i ⊆ A) (hcover : ∀ x ∈ A, LeeSviridenkoVondrak.LocalSearch.multiplicity As x = q) :
    ∃ Bs : Fin m → Finset (Fin n), (∀ i, Bs i ⊆ B) ∧
      (∀ x ∈ B, LeeSviridenkoVondrak.LocalSearch.multiplicity Bs x = q) ∧
      ∀ i, M.Indep (↑(As i ∪ (B \ Bs i)) : Set (Fin n)) := by
  classical
  by_cases hqm : q ≤ m
  · obtain ⟨C, hCJ, hCc, hCi⟩ := LSV95.core M A B hA.indep hB.indep m q hqm As hAs
      (fun x hx => le_of_eq (by simpa [LeeSviridenkoVondrak.LocalSearch.multiplicity] using hcover x hx))
    refine ⟨fun i => B \ C i, fun i => Finset.sdiff_subset, ?_, ?_⟩
    · intro x hx
      unfold LeeSviridenkoVondrak.LocalSearch.multiplicity
      have h1 := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin m))) (fun i => x ∈ C i)
      have h2 : (Finset.univ.filter (fun i => x ∈ B \ C i)) =
          Finset.univ.filter (fun i => ¬ x ∈ C i) := by
        ext i; simp [hx]
      rw [h2]
      have := hCc x hx
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      omega
    · intro i
      rw [Finset.sdiff_sdiff_eq_self (hCJ i)]
      exact hCi i
  · push Not at hqm
    have hA0 : A = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have h := hcover x hx
      unfold LeeSviridenkoVondrak.LocalSearch.multiplicity at h
      have := Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun i => x ∈ As i)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    have hB0 : B = ∅ := by
      have h := hA.encard_eq_encard_of_isBase hB
      rw [hA0, Finset.coe_empty, Set.encard_empty, Set.encard_coe_eq_coe_finsetCard] at h
      have : B.card = 0 := by exact_mod_cast h.symm
      exact Finset.card_eq_zero.1 this
    refine ⟨fun _ => ∅, fun _ => Finset.empty_subset _, ?_, ?_⟩
    · intro x hx; rw [hB0] at hx; simp at hx
    · intro i
      have : As i ∪ (B \ ∅) = ∅ := by
        rw [hB0]; have := hAs i; rw [hA0] at this
        simpa using Finset.subset_empty.1 this
      rw [this, Finset.coe_empty]
      exact M.empty_indep
