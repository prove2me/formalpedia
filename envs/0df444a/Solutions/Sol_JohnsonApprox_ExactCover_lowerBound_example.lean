-- Prove2me | solution 1 for JohnsonApprox.ExactCover.lowerBound_example
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T19:04:20.679538+00:00
-- url     : https://prove2.me/submissions/d4a46b17-3f87-46a6-a76e-c5784aaed49f

import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2
import Definitions.Def_JohnsonApprox_ExactCover_LowerBoundInput



namespace JohnsonApprox.ExactCover

open Finset

section gen
variable {α : Type} [DecidableEq α]

def stD (F : Input α) (D : Finset (Fin F.p)) : State F :=
  ⟨D, univ \ D, F.ground \ D.biUnion F.S⟩

lemma init_stD (F : Input α) : init F = stD F ∅ := by
  unfold init stD; simp

lemma step_stD (F : Input α) (D : Finset (Fin F.p)) (i : Fin F.p)
    (hne : ¬ Halts (stD F D)) (hm : MayChoose F (stD F D) i) :
    Step F (stD F D) (stD F (insert i D)) := by
  refine ⟨i, hne, hm, ?_⟩
  unfold stD
  simp only [biUnion_insert, State.mk.injEq, true_and]
  constructor
  · ext x; simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_erase]; tauto
  · ext x; simp only [mem_sdiff, mem_union]; tauto

end gen

section lb
variable (k : ℕ)

def GG : Finset (ℕ × ℕ) := Icc 1 k ×ˢ range k.factorial

lemma mem_GG {x : ℕ × ℕ} : x ∈ GG k ↔ 1 ≤ x.1 ∧ x.1 ≤ k ∧ x.2 < k.factorial := by
  simp [GG, and_assoc]

lemma mem_lbF0 {r : ℕ} {x : ℕ × ℕ} : x ∈ lbF0 k r ↔ 1 ≤ x.1 ∧ x.1 ≤ k ∧ x.2 = r := by
  unfold lbF0; simp only [mem_image, mem_Icc]; constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨hs.1, hs.2, rfl⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨x.1, ⟨h1, h2⟩, Prod.ext rfl h3.symm⟩

lemma mem_lbBlock {j q : ℕ} {x : ℕ × ℕ} : x ∈ lbBlock k j q ↔
    (x.1 = j ∧ q * j ≤ x.2 ∧ x.2 < q * j + j) ∨ (x.1 = k ∧ x.2 < k - j) := by
  unfold lbBlock; simp only [mem_union, mem_image, mem_range]
  generalize q * j = m
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · left; simp; omega
    · right; simp; omega
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · left; exact ⟨x.2 - m, by omega, Prod.ext (by simp [h1]) (by simp; omega)⟩
    · right; exact ⟨x.2, h2, Prod.ext (by simp [h1]) rfl⟩

lemma mem_lbSets {X : Finset (ℕ × ℕ)} : X ∈ lbSets k ↔
    (∃ r < k.factorial, X = lbF0 k r) ∨
    (∃ j q, 1 ≤ j ∧ j ≤ k ∧ q < k.factorial / j ∧ X = lbBlock k j q) := by
  unfold lbSets
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_range'_1]
  constructor
  · rintro (⟨r, hr, rfl⟩ | ⟨j, hj, q, hq, rfl⟩)
    · exact Or.inl ⟨r, hr, rfl⟩
    · exact Or.inr ⟨j, q, by omega, by omega, hq, rfl⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨j, q, h1, h2, hq, rfl⟩)
    · exact Or.inl ⟨r, hr, rfl⟩
    · exact Or.inr ⟨j, by omega, q, hq, rfl⟩


lemma fact_div_lt {s r : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ k) (hr : r < k.factorial) :
    r / s < k.factorial / s := by
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (by omega : 0 < s) h2
  rw [show k.factorial / s = m by rw [hm]; exact Nat.mul_div_cancel_left _ (by omega),
    Nat.div_lt_iff_lt_mul (by omega)]
  rw [hm] at hr; linarith [mul_comm s m]

lemma blk_bound {j q : ℕ} (hj : 1 ≤ j) (hq : q < k.factorial / j) : q * j + j ≤ k.factorial := by
  have h1 : (q + 1) * j ≤ k.factorial / j * j := Nat.mul_le_mul_right _ hq
  have h2 := Nat.div_mul_le_self k.factorial j
  nlinarith

lemma lbF0_card (r : ℕ) : (lbF0 k r).card = k := by
  unfold lbF0
  rw [card_image_of_injective _ (fun a b h => by simpa using h)]; simp

lemma lbBlock_card {j q : ℕ} (hj : j ≤ k) : (lbBlock k j q).card = k := by
  unfold lbBlock
  rw [card_union_of_disjoint]
  · rw [card_image_of_injective _ (fun a b h => by simpa using h),
      card_image_of_injective _ (fun a b h => by simpa using h)]
    simp; omega
  · rw [disjoint_left]
    intro x hx hx'
    simp only [mem_image, mem_range] at hx hx'
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨t', ht', he⟩ := hx'
    simp only [Prod.mk.injEq] at he
    omega

lemma lbF0_sub {r : ℕ} (hr : r < k.factorial) : lbF0 k r ⊆ GG k := by
  intro x hx; rw [mem_lbF0] at hx; rw [mem_GG]; omega

lemma lbBlock_sub {j q : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (hq : q < k.factorial / j) :
    lbBlock k j q ⊆ GG k := by
  intro x hx; rw [mem_lbBlock] at hx; rw [mem_GG]
  have := blk_bound k hj hq
  have := Nat.self_le_factorial k
  omega

lemma S_mem (i : Fin (lbInput k).p) : (lbInput k).S i ∈ lbSets k := List.get_mem _ _

lemma exists_idx {X : Finset (ℕ × ℕ)} (h : X ∈ lbSets k) : ∃ i : Fin (lbInput k).p,
    (lbInput k).S i = X := List.mem_iff_get.1 h

lemma S_card (i : Fin (lbInput k).p) : ((lbInput k).S i).card = k := by
  rcases (mem_lbSets k).1 (S_mem k i) with ⟨r, _, h⟩ | ⟨j, q, _, hj, _, h⟩
  · rw [h, lbF0_card]
  · rw [h, lbBlock_card k hj]

lemma S_sub (hk : 1 ≤ k) (i : Fin (lbInput k).p) : (lbInput k).S i ⊆ GG k := by
  rcases (mem_lbSets k).1 (S_mem k i) with ⟨r, hr, h⟩ | ⟨j, q, h1, hj, hq, h⟩
  · rw [h]; exact lbF0_sub k hr
  · rw [h]; exact lbBlock_sub k h1 hj hq

lemma ground_lb (hk : 1 ≤ k) : (lbInput k).ground = GG k := by
  apply le_antisymm
  · intro x hx; unfold Input.ground at hx; rw [mem_biUnion] at hx
    obtain ⟨i, _, hx⟩ := hx; exact S_sub k hk i hx
  · intro x hx
    obtain ⟨i, hi⟩ := exists_idx k ((mem_lbSets k).2 (Or.inl ⟨x.2, ((mem_GG k).1 hx).2.2, rfl⟩))
    unfold Input.ground; rw [mem_biUnion]
    refine ⟨i, mem_univ _, ?_⟩
    rw [hi, mem_lbF0]; rw [mem_GG] at hx; omega


def VP : Finset (ℕ × ℕ) :=
  (Icc 1 k).biUnion (fun j => (range (k.factorial / j)).image (fun q => (j, q)))

lemma mem_VP {p : ℕ × ℕ} : p ∈ VP k ↔ 1 ≤ p.1 ∧ p.1 ≤ k ∧ p.2 < k.factorial / p.1 := by
  unfold VP; simp only [mem_biUnion, mem_Icc, mem_image, mem_range]
  constructor
  · rintro ⟨j, hj, q, hq, rfl⟩; exact ⟨hj.1, hj.2, hq⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨p.1, ⟨h1, h2⟩, p.2, h3, rfl⟩

def PP (u c : ℕ) : Finset (ℕ × ℕ) := (VP k).filter (fun p => u < p.1 ∨ (p.1 = u ∧ p.2 < c))

lemma lbLen_pos : 0 < (lbInput k).p := by
  show 0 < (lbSets k).length
  unfold lbSets; simp only [List.length_append, List.length_map, List.length_range]
  have := Nat.factorial_pos k; omega

noncomputable def idx (p : ℕ × ℕ) : Fin (lbInput k).p :=
  if h : ∃ i : Fin (lbInput k).p, (lbInput k).S i = lbBlock k p.1 p.2 then h.choose
  else ⟨0, lbLen_pos k⟩

lemma S_idx {p : ℕ × ℕ} (hp : p ∈ VP k) : (lbInput k).S (idx k p) = lbBlock k p.1 p.2 := by
  rw [mem_VP] at hp
  have h : ∃ i : Fin (lbInput k).p, (lbInput k).S i = lbBlock k p.1 p.2 :=
    exists_idx k ((mem_lbSets k).2 (Or.inr ⟨p.1, p.2, hp.1, hp.2.1, hp.2.2, rfl⟩))
  unfold idx; rw [dif_pos h]; exact h.choose_spec

noncomputable def DD (u c : ℕ) : Finset (Fin (lbInput k).p) := (PP k u c).image (idx k)

lemma mem_cov (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (x : ℕ × ℕ) :
    x ∈ (DD k u c).biUnion (lbInput k).S ↔
      x ∈ GG k ∧ (u < x.1 ∨ (x.1 = u ∧ x.2 / u < c)) := by
  unfold DD; rw [image_biUnion]
  simp only [mem_biUnion]
  constructor
  · rintro ⟨p, hp, hx⟩
    unfold PP at hp; rw [mem_filter] at hp
    rw [S_idx k hp.1] at hx
    have hsub := lbBlock_sub k ((mem_VP k).1 hp.1).1 ((mem_VP k).1 hp.1).2.1
      ((mem_VP k).1 hp.1).2.2 hx
    refine ⟨hsub, ?_⟩
    have hp1 := ((mem_VP k).1 hp.1).1
    rw [mem_lbBlock] at hx
    rcases hx with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · have hq : x.2 / p.1 = p.2 := by
        exact Nat.div_eq_of_lt_le h2 (by rw [add_mul, one_mul]; exact h3)
      rw [h1] at *
      rcases hp.2 with h | ⟨h, h'⟩
      · left; exact h
      · right; rw [← h]; exact ⟨rfl, by rw [hq]; exact h'⟩
    · left; rw [h1]
      rcases hp.2 with h | ⟨h, _⟩ <;> omega
  · rintro ⟨hG, h⟩
    rw [mem_GG] at hG
    have hdiv : x.2 / x.1 < k.factorial / x.1 := fact_div_lt k hG.1 hG.2.1 hG.2.2
    refine ⟨(x.1, x.2 / x.1), ?_, ?_⟩
    · unfold PP; rw [mem_filter, mem_VP]
      refine ⟨⟨hG.1, hG.2.1, hdiv⟩, ?_⟩
      rcases h with h | ⟨h, h'⟩
      · left; exact h
      · right; refine ⟨h, ?_⟩; simp only; rw [h]; exact h'
    · rw [S_idx k (by rw [mem_VP]; exact ⟨hG.1, hG.2.1, hdiv⟩), mem_lbBlock]
      left
      exact ⟨rfl, Nat.div_mul_le_self _ _, Nat.lt_div_mul_add (by omega)⟩


lemma mem_unc (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (x : ℕ × ℕ) :
    x ∈ (lbInput k).ground \ (DD k u c).biUnion (lbInput k).S ↔
      x ∈ GG k ∧ x.1 ≤ u ∧ ¬ (x.1 = u ∧ x.2 / u < c) := by
  rw [mem_sdiff, mem_cov k u c hu huk, ground_lb k (by omega)]
  constructor
  · rintro ⟨h1, h2⟩; push_neg at h2
    refine ⟨h1, ?_, ?_⟩
    · by_contra h; exact absurd (h2 h1) (by omega)
    · rintro ⟨h3, h4⟩; have := h2 h1; omega
  · rintro ⟨h1, h2, h3⟩; refine ⟨h1, ?_⟩; rintro ⟨_, h | h⟩ <;> omega

/-- every set has at most `u` uncovered points -/
lemma unc_le (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (i : Fin (lbInput k).p) :
    ((lbInput k).S i ∩ ((lbInput k).ground \ (DD k u c).biUnion (lbInput k).S)).card ≤ u := by
  rcases (mem_lbSets k).1 (S_mem k i) with ⟨r, _, h⟩ | ⟨j, q, h1, hj, _, h⟩
  · rw [h]
    have hsub : lbF0 k r ∩ ((lbInput k).ground \ (DD k u c).biUnion (lbInput k).S) ⊆
        (Icc 1 u).image (fun s => (s, r)) := by
      intro x hx
      rw [mem_inter, mem_lbF0, mem_unc k u c hu huk] at hx
      rw [mem_image]
      exact ⟨x.1, mem_Icc.2 ⟨hx.1.1, hx.2.2.1⟩, Prod.ext rfl hx.1.2.2.symm⟩
    exact (card_le_card hsub).trans (card_image_le.trans (by simp))
  · rw [h]
    rcases Nat.lt_or_ge u k with hlt | hge
    · have hsub : lbBlock k j q ∩ ((lbInput k).ground \ (DD k u c).biUnion (lbInput k).S) ⊆
          ((range j).image (fun t => (j, q * j + t))).filter (fun x => x.1 ≤ u) := by
        intro x hx
        rw [mem_inter, mem_lbBlock, mem_unc k u c hu huk] at hx
        rw [mem_filter, mem_image]
        refine ⟨?_, hx.2.2.1⟩
        rcases hx.1 with ⟨e1, e2, e3⟩ | ⟨e1, _⟩
        · exact ⟨x.2 - q * j, mem_range.2 (by omega), Prod.ext (by simp [e1]) (by simp; omega)⟩
        · omega
      refine (card_le_card hsub).trans ?_
      rcases le_or_gt j u with hju | hju
      · exact (card_filter_le _ _).trans (card_image_le.trans (by simp; omega))
      · rw [filter_eq_empty_iff.2]; · simp
        intro x hx; rw [mem_image] at hx; obtain ⟨t, _, rfl⟩ := hx; simp; omega
    · exact (card_le_card inter_subset_left).trans (by rw [lbBlock_card k hj]; omega)

lemma unc_chosen (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (hc : c < k.factorial / u) :
    u ≤ ((lbInput k).S (idx k (u, c)) ∩
      ((lbInput k).ground \ (DD k u c).biUnion (lbInput k).S)).card := by
  have hv : (u, c) ∈ VP k := by rw [mem_VP]; exact ⟨hu, huk, hc⟩
  rw [S_idx k hv]
  have hb := blk_bound k hu hc
  have := card_le_card_of_injOn (fun t => (u, c * u + t)) (s := range u)
    (t := lbBlock k u c ∩ ((lbInput k).ground \ (DD k u c).biUnion (lbInput k).S)) (by
      intro t ht
      simp only [coe_range, Set.mem_Iio] at ht
      rw [coe_inter, Set.mem_inter_iff, mem_coe, mem_coe, mem_lbBlock, mem_unc k u c hu huk, mem_GG]
      have hd : (c * u + t) / u = c := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt ht, add_zero]
      refine ⟨Or.inl ⟨rfl, ?_, ?_⟩, ⟨⟨hu, huk, ?_⟩, le_rfl, ?_⟩⟩
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; rw [hd]; omega) (by
      intro a _ b _ hab; simp only [Prod.mk.injEq] at hab; omega)
  simpa using this

lemma maychoose (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (hc : c < k.factorial / u) :
    MayChoose (lbInput k) (stD (lbInput k) (DD k u c)) (idx k (u, c)) := by
  have hB := unc_chosen k u c hu huk hc
  have hA := unc_le k u c hu huk (idx k (u, c))
  unfold MayChoose stD
  simp only
  set U := (lbInput k).ground \ (DD k u c).biUnion (lbInput k).S
  have hne : ((lbInput k).S (idx k (u, c)) ∩ U).Nonempty := card_pos.1 (by omega)
  refine ⟨?_, hne, ?_⟩
  · rw [mem_sdiff]; refine ⟨mem_univ _, fun hD => ?_⟩
    obtain ⟨x, hx⟩ := hne
    rw [mem_inter] at hx
    exact (mem_sdiff.1 hx.2).2 (mem_biUnion.2 ⟨_, hD, hx.1⟩)
  · intro j _ _
    have hAj := unc_le k u c hu huk j
    have e1 := card_sdiff_add_card_inter ((lbInput k).S j) U
    have e2 := card_sdiff_add_card_inter ((lbInput k).S (idx k (u, c))) U
    rw [S_card] at e1 e2
    have hi : ((lbInput k).S (idx k (u, c)) ∩ U).card = u := le_antisymm hA hB
    set a := ((lbInput k).S j ∩ U).card
    set b := ((lbInput k).S j \ U).card
    set a' := ((lbInput k).S (idx k (u, c)) \ U).card
    rw [hi]
    have ha' : a' = k - u := by omega
    have hb : b = k - a := by omega
    rw [ha', hb]
    obtain ⟨d, hd⟩ : ∃ d, k = u + d := ⟨k - u, by omega⟩
    obtain ⟨e, he⟩ : ∃ e, u = a + e := ⟨u - a, by omega⟩
    rw [hd, he]
    rw [show a + e + d - (a + e) = d by omega, show a + e + d - a = e + d by omega]
    nlinarith


lemma PP_succ (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (hc : c < k.factorial / u) :
    PP k u (c + 1) = insert (u, c) (PP k u c) := by
  ext ⟨a, b⟩
  simp only [PP, mem_filter, mem_insert, mem_VP, Prod.mk.injEq]
  constructor
  · rintro ⟨hv, h | ⟨h1, h2⟩⟩
    · right; exact ⟨hv, Or.inl h⟩
    · rcases Nat.lt_or_ge b c with h3 | h3
      · right; exact ⟨hv, Or.inr ⟨h1, h3⟩⟩
      · left; omega
  · rintro (⟨rfl, rfl⟩ | ⟨hv, h | ⟨h1, h2⟩⟩)
    · exact ⟨⟨hu, huk, hc⟩, Or.inr ⟨rfl, by omega⟩⟩
    · exact ⟨hv, Or.inl h⟩
    · exact ⟨hv, Or.inr ⟨h1, by omega⟩⟩

lemma PP_top : PP k k 0 = ∅ := by
  ext ⟨a, b⟩; simp only [PP, mem_filter, mem_VP, notMem_empty, iff_false]; omega

lemma PP_next (u : ℕ) (hu : 2 ≤ u) : PP k u (k.factorial / u) = PP k (u - 1) 0 := by
  ext ⟨a, b⟩
  simp only [PP, mem_filter, mem_VP]
  constructor
  · rintro ⟨hv, h⟩; exact ⟨hv, Or.inl (by omega)⟩
  · rintro ⟨hv, h⟩
    refine ⟨hv, ?_⟩
    rcases Nat.lt_or_ge u a with h' | h'
    · exact Or.inl h'
    · right; have : a = u := by omega
      subst this; exact ⟨rfl, hv.2.2⟩

lemma PP_all : PP k 1 (k.factorial / 1) = VP k := by
  ext ⟨a, b⟩
  simp only [PP, mem_filter, mem_VP, Nat.div_one, and_iff_left_iff_imp]
  rintro ⟨h1, h2, h3⟩
  rcases Nat.lt_or_ge 1 a with h | h
  · exact Or.inl h
  · right; have : a = 1 := by omega
    subst this; simp at h3; exact ⟨rfl, h3⟩

lemma DD_succ (u c : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) (hc : c < k.factorial / u) :
    DD k u (c + 1) = insert (idx k (u, c)) (DD k u c) := by
  unfold DD; rw [PP_succ k u c hu huk hc, image_insert]

lemma reach_c (u : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) :
    ∀ c ≤ k.factorial / u, Relation.ReflTransGen (Step (lbInput k))
      (stD (lbInput k) (DD k u 0)) (stD (lbInput k) (DD k u c)) := by
  intro c
  induction c with
  | zero => intro _; exact Relation.ReflTransGen.refl
  | succ c ih =>
    intro hc
    have hc' : c < k.factorial / u := by omega
    refine (ih (by omega)).tail ?_
    rw [DD_succ k u c hu huk hc']
    apply step_stD
    · intro hh
      unfold Halts stD at hh; simp only at hh
      have hB := unc_chosen k u c hu huk hc'
      rw [hh, inter_empty, card_empty] at hB; omega
    · exact maychoose k u c hu huk hc'

lemma reach_all (hk : 1 ≤ k) : ∀ m < k, Relation.ReflTransGen (Step (lbInput k))
    (init (lbInput k)) (stD (lbInput k) (DD k (k - m) 0)) := by
  intro m
  induction m with
  | zero => intro _; rw [Nat.sub_zero, init_stD]; unfold DD; rw [PP_top, image_empty]
  | succ m ih =>
    intro hm
    have h1 := reach_c k (k - m) (by omega) (by omega) _ le_rfl
    unfold DD at h1
    rw [PP_next k (k - m) (by omega), show k - m - 1 = k - (m + 1) by omega] at h1
    exact (ih (by omega)).trans h1

lemma reach_final (hk : 1 ≤ k) : Relation.ReflTransGen (Step (lbInput k))
    (init (lbInput k)) (stD (lbInput k) (DD k 1 (k.factorial / 1))) := by
  have h1 := reach_all k hk (k - 1) (by omega)
  rw [show k - (k - 1) = 1 by omega] at h1
  exact h1.trans (reach_c k 1 le_rfl hk _ le_rfl)

lemma halts_final (hk : 1 ≤ k) : Halts (stD (lbInput k) (DD k 1 (k.factorial / 1))) := by
  unfold Halts stD; simp only
  rw [eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_unc k 1 _ le_rfl hk, mem_GG] at hx
  simp only [Nat.div_one] at hx
  omega

lemma block_inj {p p' : ℕ × ℕ} (hp : p ∈ VP k) (hp' : p' ∈ VP k)
    (h : lbBlock k p.1 p.2 = lbBlock k p'.1 p'.2) : p = p' := by
  rw [mem_VP] at hp hp'
  have pt : (p.1, p.2 * p.1) ∈ lbBlock k p.1 p.2 := by
    rw [mem_lbBlock]; left; exact ⟨rfl, le_rfl, by dsimp only; omega⟩
  have pt' : (p'.1, p'.2 * p'.1) ∈ lbBlock k p'.1 p'.2 := by
    rw [mem_lbBlock]; left; exact ⟨rfl, le_rfl, by dsimp only; omega⟩
  rw [h, mem_lbBlock] at pt
  rw [← h, mem_lbBlock] at pt'
  dsimp only at pt pt'
  rcases pt with ⟨e1, e2, e3⟩ | ⟨e1, e2⟩
  · have hq1 : p'.2 ≤ p.2 := by
      rw [e1] at e2; exact Nat.le_of_mul_le_mul_right e2 (by omega)
    have hq2 : p.2 < p'.2 + 1 := by
      rw [e1] at e3
      have : p.2 * p'.1 < (p'.2 + 1) * p'.1 := by rw [add_mul, one_mul]; exact e3
      exact Nat.lt_of_mul_lt_mul_right this
    exact Prod.ext e1 (by omega)
  · exfalso
    have hq0 : p.2 = 0 := by
      by_contra hne
      have : p.1 ≤ p.2 * p.1 := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rcases pt' with ⟨f1, _⟩ | ⟨f1, _⟩ <;> omega

noncomputable def idx0 (r : ℕ) : Fin (lbInput k).p :=
  if h : ∃ i : Fin (lbInput k).p, (lbInput k).S i = lbF0 k r then h.choose
  else ⟨0, lbLen_pos k⟩

lemma S_idx0 {r : ℕ} (hr : r < k.factorial) : (lbInput k).S (idx0 k r) = lbF0 k r := by
  have h : ∃ i : Fin (lbInput k).p, (lbInput k).S i = lbF0 k r :=
    exists_idx k ((mem_lbSets k).2 (Or.inl ⟨r, hr, rfl⟩))
  unfold idx0; rw [dif_pos h]; exact h.choose_spec

lemma measure_eq_k (M : Finset (Fin (lbInput k).p)) : (lbInput k).measure M = k * M.card := by
  unfold Input.measure; rw [sum_congr rfl (fun i _ => S_card k i), sum_const, smul_eq_mul,
    mul_comm]

lemma opt_le (hk : 1 ≤ k) : (lbInput k).opt ≤ k * k.factorial := by
  set M0 := (range k.factorial).image (idx0 k)
  have hM0 : M0 ∈ (lbInput k).subcovers := by
    unfold Input.subcovers; rw [mem_filter]; refine ⟨mem_univ _, ?_⟩
    unfold Input.IsSubcover
    apply le_antisymm
    · intro x hx; rw [mem_biUnion] at hx; obtain ⟨i, _, hx⟩ := hx
      unfold Input.ground; exact mem_biUnion.2 ⟨i, mem_univ _, hx⟩
    · intro x hx
      rw [ground_lb k hk, mem_GG] at hx
      rw [mem_biUnion]
      refine ⟨idx0 k x.2, mem_image.2 ⟨x.2, mem_range.2 hx.2.2, rfl⟩, ?_⟩
      rw [S_idx0 k hx.2.2, mem_lbF0]; omega
  calc (lbInput k).opt ≤ (lbInput k).measure M0 := inf'_le _ hM0
    _ = k * M0.card := measure_eq_k k M0
    _ ≤ k * k.factorial := Nat.mul_le_mul_left _ (card_image_le.trans (by simp))

lemma card_VP : (VP k).card = ∑ j ∈ Icc 1 k, k.factorial / j := by
  unfold VP
  rw [card_biUnion]
  · apply sum_congr rfl; intro j _
    rw [card_image_of_injective _ (fun a b h => by simpa using h), card_range]
  · intro a _ b _ hab
    rw [Function.onFun, disjoint_left]
    intro x hx hx'
    rw [mem_image] at hx hx'
    obtain ⟨_, _, rfl⟩ := hx; obtain ⟨_, _, he⟩ := hx'
    simp only [Prod.mk.injEq] at he; exact hab he.1.symm

lemma ground_le_measure' (F : Input (ℕ × ℕ)) (M : Finset (Fin F.p)) (hM : F.IsSubcover M) :
    F.ground.card ≤ F.measure M := by
  unfold Input.IsSubcover at hM; rw [← hM]; exact card_biUnion_le

lemma ground_le_opt' (F : Input (ℕ × ℕ)) : F.ground.card ≤ F.opt := by
  unfold Input.opt; apply le_inf'; intro M hM
  unfold Input.subcovers at hM; rw [mem_filter] at hM
  exact ground_le_measure' F M hM.2

end lb

theorem lowerBound_example (k : ℕ) (hk : 1 ≤ k) :
    (∀ i, ((lbInput k).S i).card = k) ∧ InEC k (lbInput k) ∧ 0 < (lbInput k).opt ∧
      ∃ M, Choosable (lbInput k) M ∧
        (harmonic k : ℝ) * (lbInput k).opt ≤ (lbInput k).measure M := by
  refine ⟨S_card k, fun i => (S_card k i).le, ?_, ?_⟩
  · refine lt_of_lt_of_le ?_ (ground_le_opt' _)
    rw [ground_lb k hk]; apply card_pos.2
    exact ⟨(1, 0), by rw [mem_GG]; exact ⟨le_rfl, hk, Nat.factorial_pos k⟩⟩
  · refine ⟨DD k 1 (k.factorial / 1), ⟨_, reach_final k hk, halts_final k hk, rfl⟩, ?_⟩
    rw [measure_eq_k]
    have hcard : (DD k 1 (k.factorial / 1)).card = ∑ j ∈ Icc 1 k, k.factorial / j := by
      unfold DD; rw [PP_all, card_image_of_injOn, card_VP]
      intro p hp p' hp' he
      have := congrArg (lbInput k).S he
      rw [S_idx k hp, S_idx k hp'] at this
      exact block_inj k hp hp' this
    rw [hcard]
    have hopt := opt_le k hk
    have hsum : ((∑ j ∈ Icc 1 k, k.factorial / j : ℕ) : ℝ) = k.factorial * (harmonic k : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast
      rw [mul_sum]; apply sum_congr rfl; intro j hj
      rw [mem_Icc] at hj
      rw [Nat.cast_div (Nat.dvd_factorial (by omega) hj.2) (by norm_cast; omega)]
      field_simp
    push_cast [hsum]
    have hH : (0 : ℝ) ≤ harmonic k := by
      have : (0 : ℚ) ≤ harmonic k := by
        unfold harmonic; exact sum_nonneg (fun i _ => by positivity)
      exact_mod_cast this
    have : ((lbInput k).opt : ℝ) ≤ k * k.factorial := by exact_mod_cast hopt
    calc (harmonic k : ℝ) * (lbInput k).opt ≤ (harmonic k : ℝ) * (k * k.factorial) :=
          mul_le_mul_of_nonneg_left this hH
      _ = k * (k.factorial * harmonic k) := by ring

end JohnsonApprox.ExactCover

open JohnsonApprox.ExactCover

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    (∀ i, ((lbInput k).S i).card = k) ∧ InEC k (lbInput k) ∧ 0 < (lbInput k).opt ∧
      ∃ M, Choosable (lbInput k) M ∧
        (harmonic k : ℝ) * (lbInput k).opt ≤ (lbInput k).measure M := by
  exact lowerBound_example k hk
