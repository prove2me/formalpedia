-- Prove2me | solution 1 for GivenDegreeSeq.Interior.erdos_gallai
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:44:03.385185+00:00
-- url     : https://prove2.me/submissions/79f0ca16-18ca-48a4-a81e-5bb50ef68907

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_IsGraphic

set_option autoImplicit false

open GivenDegreeSeq.Interior

open Finset

section EGHelpers

open Classical

variable {n : ℕ}

/-! ### Degrees as cardinalities of adjacency filters -/

private noncomputable def dg (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (univ.filter (G.Adj v)).card

private lemma degree_eq_dg (G : SimpleGraph (Fin n)) (v : Fin n) [Fintype (G.neighborSet v)] :
    G.degree v = dg G v := by
  rw [← G.card_neighborSet_eq_degree, Fintype.card_subtype]; rfl

private lemma dg_eq_sum (G : SimpleGraph (Fin n)) (v : Fin n) :
    dg G v = ∑ w, if G.Adj v w then 1 else 0 := by
  unfold dg; rw [Finset.card_filter]

private lemma dg_eq_sumZ (G : SimpleGraph (Fin n)) (v : Fin n) :
    (dg G v : ℤ) = ∑ w, if G.Adj v w then (1 : ℤ) else 0 := by
  rw [dg_eq_sum]; push_cast; rfl

private lemma sum_dg (G : SimpleGraph (Fin n)) : ∑ v, dg G v = 2 * G.edgeFinset.card := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  exact Finset.sum_congr rfl (fun v _ => (degree_eq_dg G v).symm)

private lemma card_filter_lt (k : ℕ) (hk : k ≤ n) :
    (univ.filter (fun i : Fin n => (i : ℕ) < k)).card = k := by
  have : (univ.filter (fun i : Fin n => (i : ℕ) < k)) =
      (Finset.range k).attachFin (fun m hm => by simp at hm; omega) := by
    ext i; simp
  rw [this, Finset.card_attachFin, Finset.card_range]

/-! ### Modifying a graph by removing and adding a few edges -/

private def modG (G : SimpleGraph (Fin n)) (R A : List (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ ((G.Adj x y ∧ ∀ p ∈ R, s(x, y) ≠ s(p.1, p.2)) ∨ ∃ p ∈ A, s(x, y) = s(p.1, p.2))
  symm := ⟨by
    intro x y h
    obtain ⟨h1, h2⟩ := h
    have e : s(y, x) = s(x, y) := Sym2.eq_swap
    refine ⟨h1.symm, ?_⟩
    rw [e]
    rcases h2 with ⟨h, h'⟩ | h
    · exact Or.inl ⟨h.symm, h'⟩
    · exact Or.inr h⟩
  loopless := ⟨fun x h => h.1 rfl⟩

private lemma modG_adj (G : SimpleGraph (Fin n)) (R A : List (Fin n × Fin n)) (x y : Fin n) :
    (modG G R A).Adj x y ↔
      (x ≠ y ∧ ((G.Adj x y ∧ ∀ p ∈ R, s(x, y) ≠ s(p.1, p.2)) ∨ ∃ p ∈ A, s(x, y) = s(p.1, p.2))) :=
  Iff.rfl

private def iv (v a : Fin n) : ℤ := if v = a then 1 else 0

private def ind (v : Fin n) (p : Fin n × Fin n) : ℤ := iv v p.1 + iv v p.2

private lemma sum_sym2_ind (v a b : Fin n) (hab : a ≠ b) :
    (∑ w, if s(v, w) = s(a, b) then (1 : ℤ) else 0) = ind v (a, b) := by
  simp only [Sym2.eq_iff, ind, iv]
  by_cases hva : v = a
  · subst hva
    have hvb : ¬ v = b := hab
    simp [hvb]
  · by_cases hvb : v = b
    · subst hvb
      simp [hva]
    · simp [hva, hvb]

private lemma ite_exists_eq_sum (e : Sym2 (Fin n)) (R : List (Fin n × Fin n))
    (hR : R.Pairwise (fun p q => s(p.1, p.2) ≠ s(q.1, q.2))) :
    (if ∃ p ∈ R, e = s(p.1, p.2) then (1 : ℤ) else 0) =
      (R.map (fun p => if e = s(p.1, p.2) then (1 : ℤ) else 0)).sum := by
  induction R with
  | nil => simp
  | cons p R ih =>
    rw [List.pairwise_cons] at hR
    rw [List.map_cons, List.sum_cons, ← ih hR.2]
    by_cases h : e = s(p.1, p.2)
    · have hn : ¬ ∃ q ∈ R, e = s(q.1, q.2) := by
        rintro ⟨q, hq, he⟩
        exact hR.1 q hq (h.symm.trans he)
      rw [if_pos ⟨p, List.mem_cons_self, h⟩, if_pos h, if_neg hn]; ring
    · have hiff : (∃ q ∈ p :: R, e = s(q.1, q.2)) ↔ ∃ q ∈ R, e = s(q.1, q.2) := by
        constructor
        · rintro ⟨q, hq, he⟩
          rcases List.mem_cons.mp hq with hq | hq
          · subst hq; exact absurd he h
          · exact ⟨q, hq, he⟩
        · rintro ⟨q, hq, he⟩; exact ⟨q, List.mem_cons_of_mem _ hq, he⟩
      rw [if_neg h]
      by_cases h2 : ∃ q ∈ R, e = s(q.1, q.2)
      · rw [if_pos (hiff.mpr h2), if_pos h2]; ring
      · rw [if_neg (fun h' => h2 (hiff.mp h')), if_neg h2]; ring

private lemma sum_list_comm (R : List (Fin n × Fin n)) (f : Fin n × Fin n → Fin n → ℤ) :
    (∑ w, (R.map (fun p => f p w)).sum) = (R.map (fun p => ∑ w, f p w)).sum := by
  induction R with
  | nil => simp
  | cons p R ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

private lemma sum_ind_list (v : Fin n) (R : List (Fin n × Fin n))
    (hR : R.Pairwise (fun p q => s(p.1, p.2) ≠ s(q.1, q.2))) (hne : ∀ p ∈ R, p.1 ≠ p.2) :
    (∑ w, if ∃ p ∈ R, s(v, w) = s(p.1, p.2) then (1 : ℤ) else 0) = (R.map (ind v)).sum := by
  rw [Finset.sum_congr rfl (fun w _ => ite_exists_eq_sum (s(v, w)) R hR)]
  rw [sum_list_comm R (fun p w => if s(v, w) = s(p.1, p.2) then (1 : ℤ) else 0)]
  congr 1
  apply List.map_congr_left
  intro p hp
  exact sum_sym2_ind v p.1 p.2 (hne p hp)

private lemma dg_modG (G : SimpleGraph (Fin n)) (R A : List (Fin n × Fin n))
    (hRp : R.Pairwise (fun p q => s(p.1, p.2) ≠ s(q.1, q.2)))
    (hAp : A.Pairwise (fun p q => s(p.1, p.2) ≠ s(q.1, q.2)))
    (hR : ∀ p ∈ R, G.Adj p.1 p.2) (hA : ∀ p ∈ A, p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2) (v : Fin n) :
    (dg (modG G R A) v : ℤ) = dg G v - (R.map (ind v)).sum + (A.map (ind v)).sum := by
  have key : ∀ w, (if (modG G R A).Adj v w then (1 : ℤ) else 0) =
      (if G.Adj v w then 1 else 0) - (if ∃ p ∈ R, s(v, w) = s(p.1, p.2) then 1 else 0)
        + (if ∃ p ∈ A, s(v, w) = s(p.1, p.2) then 1 else 0) := by
    intro w
    by_cases h1 : ∃ p ∈ R, s(v, w) = s(p.1, p.2)
    · obtain ⟨p, hp, he⟩ := h1
      have hadj : G.Adj v w := by
        rw [← SimpleGraph.mem_edgeSet, he, SimpleGraph.mem_edgeSet]; exact hR p hp
      have hnA : ¬ ∃ q ∈ A, s(v, w) = s(q.1, q.2) := by
        rintro ⟨q, hq, he'⟩
        apply (hA q hq).2
        rw [← SimpleGraph.mem_edgeSet, ← he', SimpleGraph.mem_edgeSet]; exact hadj
      have hnM : ¬ (modG G R A).Adj v w := by
        rw [modG_adj]
        rintro ⟨_, ⟨_, h⟩ | h⟩
        · exact h p hp he
        · exact hnA h
      rw [if_neg hnM, if_pos hadj, if_pos ⟨p, hp, he⟩, if_neg hnA]; ring
    · by_cases h2 : ∃ p ∈ A, s(v, w) = s(p.1, p.2)
      · obtain ⟨p, hp, he⟩ := h2
        have hnadj : ¬ G.Adj v w := by
          intro hadj; apply (hA p hp).2
          rw [← SimpleGraph.mem_edgeSet, ← he, SimpleGraph.mem_edgeSet]; exact hadj
        have hvw : v ≠ w := by
          intro hvw; subst hvw; apply (hA p hp).1
          have hd : s(v, v).IsDiag := Sym2.mk_isDiag_iff.mpr rfl
          rw [he] at hd; exact Sym2.mk_isDiag_iff.mp hd
        have hM : (modG G R A).Adj v w := (modG_adj _ _ _ _ _).mpr ⟨hvw, Or.inr ⟨p, hp, he⟩⟩
        rw [if_pos hM, if_neg hnadj, if_neg h1, if_pos ⟨p, hp, he⟩]; ring
      · rw [if_neg h1, if_neg h2]
        by_cases hG : G.Adj v w
        · have hM : (modG G R A).Adj v w :=
            ⟨G.ne_of_adj hG, Or.inl ⟨hG, fun p hp he => h1 ⟨p, hp, he⟩⟩⟩
          rw [if_pos hM, if_pos hG]; ring
        · have hM : ¬ (modG G R A).Adj v w := by
            rintro ⟨_, ⟨h, _⟩ | h⟩
            · exact hG h
            · exact h2 h
          rw [if_neg hM, if_neg hG]; ring
  rw [dg_eq_sumZ, dg_eq_sumZ, Finset.sum_congr rfl (fun w _ => key w)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_ind_list v R hRp (fun p hp => G.ne_of_adj (hR p hp)),
    sum_ind_list v A hAp (fun p hp => (hA p hp).1)]

/-! ### Improvement steps -/

/-- `G'` improves `G` at the critical vertex `r`: still a subrealisation of `d`, vertices before
`r` stay saturated, and the degree of `r` grows. -/
private def Good (d : Fin n → ℕ) (r : Fin n) (G G' : SimpleGraph (Fin n)) : Prop :=
  (∀ v, dg G' v ≤ d v) ∧ (∀ i : Fin n, i.val < r.val → dg G' i = d i) ∧ dg G r < dg G' r

private lemma iv_self (v : Fin n) : iv v v = 1 := by simp [iv]

private lemma iv_ne {v a : Fin n} (h : v ≠ a) : iv v a = 0 := by simp [iv, h]

private lemma ne_of_val_lt {a b : Fin n} (h : a.val < b.val) : a ≠ b := by
  intro e; subst e; omega

/-- `r` gains one, `x` (after `r`) loses one. -/
private lemma finish_minus (d : Fin n → ℕ) (r x : Fin n) (G G' : SimpleGraph (Fin n))
    (hG : ∀ v, dg G v ≤ d v) (hL : ∀ i : Fin n, i.val < r.val → dg G i = d i)
    (hr : dg G r < d r) (hx : r.val < x.val)
    (hf : ∀ v, (dg G' v : ℤ) = dg G v + iv v r - iv v x) : Good d r G G' := by
  have hrx : r ≠ x := ne_of_val_lt hx
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have h := hf v
    have := hG v
    by_cases h1 : v = r
    · subst h1; rw [iv_self, iv_ne hrx] at h; omega
    · by_cases h2 : v = x
      · subst h2; rw [iv_self, iv_ne h1] at h; omega
      · rw [iv_ne h1, iv_ne h2] at h; omega
  · intro i hi
    have h := hf i
    have := hL i hi
    rw [iv_ne (ne_of_val_lt hi), iv_ne (ne_of_val_lt (lt_trans hi hx))] at h; omega
  · have h := hf r
    rw [iv_self, iv_ne hrx] at h; omega

/-- `r` gains one, and a deficient `k` (after `r`) gains one. -/
private lemma finish_plus (d : Fin n → ℕ) (r k : Fin n) (G G' : SimpleGraph (Fin n))
    (hG : ∀ v, dg G v ≤ d v) (hL : ∀ i : Fin n, i.val < r.val → dg G i = d i)
    (hr : dg G r < d r) (hk : r.val < k.val) (hdk : dg G k < d k)
    (hf : ∀ v, (dg G' v : ℤ) = dg G v + iv v r + iv v k) : Good d r G G' := by
  have hrk : r ≠ k := ne_of_val_lt hk
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have h := hf v
    have := hG v
    by_cases h1 : v = r
    · subst h1; rw [iv_self, iv_ne hrk] at h; omega
    · by_cases h2 : v = k
      · subst h2; rw [iv_self, iv_ne h1] at h; omega
      · rw [iv_ne h1, iv_ne h2] at h; omega
  · intro i hi
    have h := hf i
    have := hL i hi
    rw [iv_ne (ne_of_val_lt hi), iv_ne (ne_of_val_lt (lt_trans hi hk))] at h; omega
  · have h := hf r
    rw [iv_self, iv_ne hrk] at h; omega

/-- `r` gains two. -/
private lemma finish_two (d : Fin n → ℕ) (r : Fin n) (G G' : SimpleGraph (Fin n))
    (hG : ∀ v, dg G v ≤ d v) (hL : ∀ i : Fin n, i.val < r.val → dg G i = d i)
    (hr : dg G r + 2 ≤ d r)
    (hf : ∀ v, (dg G' v : ℤ) = dg G v + 2 * iv v r) : Good d r G G' := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have h := hf v
    have := hG v
    by_cases h1 : v = r
    · subst h1; rw [iv_self] at h; omega
    · rw [iv_ne h1] at h; omega
  · intro i hi
    have h := hf i
    have := hL i hi
    rw [iv_ne (ne_of_val_lt hi)] at h; omega
  · have h := hf r
    rw [iv_self] at h; omega

/-- A saturated vertex of larger degree than `r` has a neighbour outside `N[r]`. -/
private lemma exists_u (G : SimpleGraph (Fin n)) (i r : Fin n) (hir : i ≠ r)
    (hlt : dg G r < dg G i) : ∃ u, G.Adj i u ∧ ¬ G.Adj r u ∧ u ≠ r := by
  by_contra hcon
  push Not at hcon
  have hsub : (univ.filter (G.Adj i)).erase r ⊆ (univ.filter (G.Adj r)).erase i := by
    intro u hu
    simp only [mem_erase, mem_filter, mem_univ, true_and] at hu ⊢
    refine ⟨?_, ?_⟩
    · rintro rfl; exact G.loopless.irrefl _ hu.2
    · by_contra h; exact hu.1 (hcon u hu.2 h)
  have hc := card_le_card hsub
  unfold dg at hlt
  by_cases hadj : G.Adj i r
  · rw [card_erase_of_mem (by simp [hadj]), card_erase_of_mem (by simp [hadj.symm])] at hc
    have h1 : 0 < (univ.filter (G.Adj r)).card := card_pos.mpr ⟨i, by simp [hadj.symm]⟩
    omega
  · rw [erase_eq_of_notMem (by simp [hadj]),
      erase_eq_of_notMem (by simpa using fun h : G.Adj r i => hadj h.symm)] at hc
    omega

/-- Parity: if only `r` is deficient, its deficiency is not one. -/
private lemma exists_deficient (d : Fin n → ℕ) (G : SimpleGraph (Fin n)) (r : Fin n)
    (heven : Even (∑ i, d i)) (hG : ∀ v, dg G v ≤ d v) (hr : dg G r + 1 = d r) :
    ∃ k, k ≠ r ∧ dg G k < d k := by
  by_contra hcon
  push Not at hcon
  have hrest : ∑ i ∈ univ.erase r, d i = ∑ i ∈ univ.erase r, dg G i := by
    apply sum_congr rfl
    intro i hi
    have := hcon i (ne_of_mem_erase hi)
    have := hG i
    omega
  have hsum : ∑ i, d i = ∑ i, dg G i + 1 := by
    rw [← Finset.add_sum_erase _ _ (mem_univ r), ← Finset.add_sum_erase _ _ (mem_univ r), hrest]
    omega
  rw [hsum, sum_dg] at heven
  exact (Nat.even_add_one.mp heven) (even_two_mul _)

/-! ### The seven local moves -/

section Moves

variable (d : Fin n → ℕ) (G : SimpleGraph (Fin n)) (r : Fin n)
  (hG : ∀ v, dg G v ≤ d v) (hL : ∀ i : Fin n, i.val < r.val → dg G i = d i)
  (hr : dg G r < d r)
include hG hL hr

/-- Add the edge `rk` to a deficient `k`. -/
private lemma move0 (k : Fin n) (hk : r.val < k.val) (hdk : dg G k < d k) (hrk : ¬ G.Adj r k) :
    ∃ G', Good d r G G' := by
  have hne : r ≠ k := ne_of_val_lt hk
  refine ⟨modG G [] [(r, k)], finish_plus d r k G _ hG hL hr hk hdk (fun v => ?_)⟩
  rw [dg_modG G [] [(r, k)] (by simp) (by simp) (by simp) (by simp [hne, hrk])]
  simp only [ind, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

omit hr in
/-- `i < r` non-adjacent to `r`, `u ∈ N(i) \ N[r]`, deficiency of `r` at least two:
replace `iu` by `ir, ur`. -/
private lemma move1a (i u : Fin n) (hi : i.val < r.val) (hri : ¬ G.Adj r i) (hiu : G.Adj i u)
    (hru : ¬ G.Adj r u) (hur : u ≠ r) (h2 : dg G r + 2 ≤ d r) : ∃ G', Good d r G G' := by
  have hir : i ≠ r := ne_of_val_lt hi
  have hiu' : i ≠ u := G.ne_of_adj hiu
  have hru' : ¬ G.Adj u r := fun h => hru h.symm
  have hri' : ¬ G.Adj i r := fun h => hri h.symm
  refine ⟨modG G [(i, u)] [(i, r), (u, r)], finish_two d r G _ hG hL h2 (fun v => ?_)⟩
  rw [dg_modG G [(i, u)] [(i, r), (u, r)] (by simp)
    (by simp [hiu', hir]) (by simp [hiu])
    (by simp [hir, hur, hri', hru'])]
  simp only [ind, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- As `move1a`, but stealing the edge `rk` for some `k > r` adjacent to `r`. -/
private lemma move1b (i u k : Fin n) (hi : i.val < r.val) (hri : ¬ G.Adj r i) (hiu : G.Adj i u)
    (hru : ¬ G.Adj r u) (hur : u ≠ r) (hk : r.val < k.val) (hrk : G.Adj r k) :
    ∃ G', Good d r G G' := by
  have hir : i ≠ r := ne_of_val_lt hi
  have hik : i ≠ k := ne_of_val_lt (lt_trans hi hk)
  have hiu' : i ≠ u := G.ne_of_adj hiu
  have hru' : ¬ G.Adj u r := fun h => hru h.symm
  have hri' : ¬ G.Adj i r := fun h => hri h.symm
  refine ⟨modG G [(i, u), (r, k)] [(i, r), (u, r)],
    finish_minus d r k G _ hG hL hr hk (fun v => ?_)⟩
  rw [dg_modG G [(i, u), (r, k)] [(i, r), (u, r)] (by simp [hir, hik])
    (by simp [hiu', hir]) (by simp [hiu, hrk])
    (by simp [hir, hur, hri', hru'])]
  simp only [ind, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- `k > r` with a neighbour `x ∉ N[r]`: replace `kx` by `rx`. -/
private lemma move2 (k x : Fin n) (hk : r.val < k.val) (hkx : G.Adj k x) (hxr : x ≠ r)
    (hrx : ¬ G.Adj r x) : ∃ G', Good d r G G' := by
  have hrx' : r ≠ x := fun h => hxr h.symm
  refine ⟨modG G [(k, x)] [(r, x)], finish_minus d r k G _ hG hL hr hk (fun v => ?_)⟩
  rw [dg_modG G [(k, x)] [(r, x)] (by simp) (by simp) (by simp [hkx]) (by simp [hrx', hrx])]
  simp only [ind, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- `i, j < r` non-adjacent, `u ∈ N(i) \ N[r]`, `w ∈ N(j) \ N[r]` with `w > r`:
replace `iu, jw` by `ij, ur`. -/
private lemma movea (i j u w : Fin n) (hi : i.val < r.val) (_hj : j.val < r.val) (hij : i ≠ j)
    (hnij : ¬ G.Adj i j) (hiu : G.Adj i u) (hjw : G.Adj j w) (hru : ¬ G.Adj r u) (hur : u ≠ r)
    (hw : r.val < w.val) : ∃ G', Good d r G G' := by
  have hir : i ≠ r := ne_of_val_lt hi
  have hiw : i ≠ w := ne_of_val_lt (lt_trans hi hw)
  have hiu' : i ≠ u := G.ne_of_adj hiu
  have hru' : ¬ G.Adj u r := fun h => hru h.symm
  refine ⟨modG G [(i, u), (j, w)] [(i, j), (u, r)],
    finish_minus d r w G _ hG hL hr hw (fun v => ?_)⟩
  rw [dg_modG G [(i, u), (j, w)] [(i, j), (u, r)] (by simp [hij, hiw])
    (by simp [hiu', hir]) (by simp [hiu, hjw])
    (by simp [hij, hur, hnij, hru'])]
  simp only [ind, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- `j < r`, deficient `k > r` adjacent to `r` but not to `j`, `u ∈ N(j) \ N[r]`:
replace `ju` by `jk, ur`. -/
private lemma movebd (j k u : Fin n) (hj : j.val < r.val) (hk : r.val < k.val)
    (hdk : dg G k < d k) (hnjk : ¬ G.Adj j k) (hju : G.Adj j u) (hru : ¬ G.Adj r u)
    (hur : u ≠ r) : ∃ G', Good d r G G' := by
  have hjr : j ≠ r := ne_of_val_lt hj
  have hjk : j ≠ k := ne_of_val_lt (lt_trans hj hk)
  have hju' : j ≠ u := G.ne_of_adj hju
  have hru' : ¬ G.Adj u r := fun h => hru h.symm
  refine ⟨modG G [(j, u)] [(j, k), (u, r)],
    finish_plus d r k G _ hG hL hr hk hdk (fun v => ?_)⟩
  rw [dg_modG G [(j, u)] [(j, k), (u, r)] (by simp)
    (by simp [hju', hjr]) (by simp [hju])
    (by simp [hjk, hur, hnjk, hru'])]
  simp only [ind, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- `j < r`, `k > r` not adjacent to `j`, with a neighbour `y > r`; `u ∈ N(j) \ N[r]`:
replace `ju, ky` by `jk, ur`. -/
private lemma moveby (j k u y : Fin n) (hj : j.val < r.val) (hk : r.val < k.val)
    (hy : r.val < y.val) (hky : G.Adj k y) (hnjk : ¬ G.Adj j k) (hju : G.Adj j u)
    (hru : ¬ G.Adj r u) (hur : u ≠ r) : ∃ G', Good d r G G' := by
  have hjr : j ≠ r := ne_of_val_lt hj
  have hjk : j ≠ k := ne_of_val_lt (lt_trans hj hk)
  have hjy : j ≠ y := ne_of_val_lt (lt_trans hj hy)
  have hju' : j ≠ u := G.ne_of_adj hju
  have hru' : ¬ G.Adj u r := fun h => hru h.symm
  refine ⟨modG G [(j, u), (k, y)] [(j, k), (u, r)],
    finish_minus d r y G _ hG hL hr hy (fun v => ?_)⟩
  rw [dg_modG G [(j, u), (k, y)] [(j, k), (u, r)] (by simp [hjk, hjy])
    (by simp [hju', hjr]) (by simp [hju, hky])
    (by simp [hjk, hur, hnjk, hru'])]
  simp only [ind, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

end Moves

/-! ### Double counting around the first `k` vertices -/

private lemma ite_adj_comm (G : SimpleGraph (Fin n)) (i w : Fin n) :
    (if G.Adj i w then 1 else 0 : ℕ) = if G.Adj w i then 1 else 0 := by
  by_cases h : G.Adj i w
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

private lemma sum_split (G : SimpleGraph (Fin n)) (k : ℕ) :
    ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), dg G i =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k),
          ∑ w ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), (if G.Adj i w then 1 else 0)
        + ∑ w ∈ univ.filter (fun j : Fin n => k ≤ (j : ℕ)),
          ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), (if G.Adj w i then 1 else 0) := by
  have h1 : ∀ i, dg G i =
      ∑ w ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), (if G.Adj i w then 1 else 0)
      + ∑ w ∈ univ.filter (fun j : Fin n => k ≤ (j : ℕ)), (if G.Adj i w then 1 else 0) := by
    intro i
    rw [dg_eq_sum, ← sum_filter_add_sum_filter_not univ (fun w : Fin n => (w : ℕ) < k)]
    congr 1
    exact sum_congr (by ext; simp) (fun _ _ => rfl)
  rw [sum_congr rfl (fun i _ => h1 i), sum_add_distrib]
  congr 1
  rw [sum_comm]
  exact sum_congr rfl (fun w _ => sum_congr rfl (fun i _ => ite_adj_comm G i w))

private lemma sum_row_eq_card (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (i : Fin n) :
    ∑ w ∈ S, (if G.Adj i w then 1 else 0) = (S.filter (G.Adj i)).card := by
  rw [card_filter]

private lemma sum_row_le (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    ∑ w ∈ S, (if G.Adj i w then 1 else 0) ≤ S.card - 1 := by
  rw [sum_row_eq_card, ← card_erase_of_mem hi]
  apply card_le_card
  intro w hw
  simp only [mem_filter] at hw
  exact mem_erase.mpr ⟨(G.ne_of_adj hw.2).symm, hw.1⟩

private lemma sum_row_clique (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (i : Fin n)
    (hi : i ∈ S) (hcl : ∀ w ∈ S, w ≠ i → G.Adj i w) :
    ∑ w ∈ S, (if G.Adj i w then 1 else 0) = S.card - 1 := by
  rw [sum_row_eq_card, ← card_erase_of_mem hi]
  congr 1
  ext w
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨hw, hadj⟩; exact ⟨(G.ne_of_adj hadj).symm, hw⟩
  · rintro ⟨hne, hw⟩; exact ⟨hw, hcl w hw hne⟩

private lemma sum_row_le_dg (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (i : Fin n) :
    ∑ w ∈ S, (if G.Adj i w then 1 else 0) ≤ dg G i := by
  rw [sum_row_eq_card]
  unfold dg
  apply card_le_card
  intro w hw
  simp only [mem_filter, mem_univ, true_and] at hw ⊢
  exact hw.2

private lemma sum_row_le_card (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (i : Fin n) :
    ∑ w ∈ S, (if G.Adj i w then 1 else 0) ≤ S.card := by
  rw [sum_row_eq_card]; exact card_filter_le _ _

private def EGcond (d : Fin n → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ n →
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), d i ≤
      k * (k - 1) + ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), min (d i) k

/-! ### The improvement lemma -/

private lemma improve (d : Fin n → ℕ) (hd : Antitone d) (heven : Even (∑ i, d i))
    (hEG : EGcond d) (G : SimpleGraph (Fin n)) (r : Fin n) (hG : ∀ v, dg G v ≤ d v)
    (hL : ∀ i : Fin n, i.val < r.val → dg G i = d i) (hr : dg G r < d r) :
    ∃ G', Good d r G G' := by
  by_contra hno
  have hU : ∀ i : Fin n, i.val < r.val → ∃ u, G.Adj i u ∧ ¬ G.Adj r u ∧ u ≠ r := by
    intro i hi
    apply exists_u G i r (ne_of_val_lt hi)
    have : d r ≤ d i := hd (Fin.le_iff_val_le_val.mpr (le_of_lt hi))
    have := hL i hi
    omega
  -- (N1) `r` is adjacent to every earlier vertex.
  have N1 : ∀ i : Fin n, i.val < r.val → G.Adj r i := by
    intro i hi
    by_contra hri
    obtain ⟨u, hiu, hru, hur⟩ := hU i hi
    by_cases h2 : dg G r + 2 ≤ d r
    · exact hno (move1a d G r hG hL i u hi hri hiu hru hur h2)
    · obtain ⟨k, hkr, hk⟩ := exists_deficient d G r heven hG (by omega)
      have hrk : r.val < k.val := by
        rcases lt_trichotomy k.val r.val with h | h | h
        · have := hL k h; omega
        · exact absurd (Fin.ext h) hkr
        · exact h
      by_cases hadj : G.Adj r k
      · exact hno (move1b d G r hG hL hr i u k hi hri hiu hru hur hrk hadj)
      · exact hno (move0 d G r hG hL hr k hrk hk hadj)
  -- (N2) every later vertex has all its neighbours in `N[r]`.
  have N2 : ∀ k : Fin n, r.val < k.val → ∀ x, G.Adj k x → x = r ∨ G.Adj r x := by
    intro k hk x hkx
    by_contra h
    push Not at h
    exact hno (move2 d G r hG hL hr k x hk hkx h.1 h.2)
  -- (Na) the earlier vertices form a clique.
  have Na : ∀ i j : Fin n, i.val < r.val → j.val < r.val → i ≠ j → G.Adj i j := by
    intro i j hi hj hij
    by_contra hnij
    obtain ⟨u, hiu, hru, hur⟩ := hU i hi
    obtain ⟨w, hjw, hrw, hwr⟩ := hU j hj
    have hw : r.val < w.val := by
      rcases lt_trichotomy w.val r.val with h | h | h
      · exact absurd (N1 w h) hrw
      · exact absurd (Fin.ext h) hwr
      · exact h
    exact hno (movea d G r hG hL hr i j u w hi hj hij hnij hiu hjw hru hur hw)
  -- (Nb) a later vertex sees all of `S`, or is saturated with all neighbours in `S`.
  have Nb : ∀ k : Fin n, r.val < k.val →
      (∀ j : Fin n, j.val ≤ r.val → G.Adj k j) ∨
        ((∀ y, G.Adj k y → y.val ≤ r.val) ∧ dg G k = d k) := by
    intro k hk
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨j, hjr, hkj⟩, hcon2⟩ := hcon
    have hdef_or : dg G k < d k ∨ ∃ y, G.Adj k y ∧ r.val < y.val := by
      by_cases hy : ∃ y, G.Adj k y ∧ r.val < y.val
      · exact Or.inr hy
      · left
        push Not at hy
        have := hcon2 hy
        have := hG k
        omega
    have hrk : G.Adj r k := by
      by_contra hrk
      rcases hdef_or with hdef | ⟨y, hky, hy⟩
      · exact hno (move0 d G r hG hL hr k hk hdef hrk)
      · rcases N2 y hy k hky.symm with h | h
        · exact absurd h (ne_of_val_lt hk).symm
        · exact hrk h
    have hjr' : j.val < r.val := by
      rcases lt_or_eq_of_le hjr with h | h
      · exact h
      · exact absurd (by rw [Fin.ext h]; exact hrk.symm) hkj
    obtain ⟨u, hju, hru, hur⟩ := hU j hjr'
    have hnjk : ¬ G.Adj j k := fun h => hkj h.symm
    rcases hdef_or with hdef | ⟨y, hky, hy⟩
    · exact hno (movebd d G r hG hL hr j k u hjr' hk hdef hnjk hju hru hur)
    · exact hno (moveby d G r hG hL hr j k u y hjr' hk hy hky hnjk hju hru hur)
  -- Counting: the Erdős–Gallai inequality at `k = r + 1` is violated.
  have hkn : r.val + 1 ≤ n := r.isLt
  have hEGk := hEG (r.val + 1) (by omega) hkn
  have hsplit := sum_split G (r.val + 1)
  have hcard := card_filter_lt (n := n) (r.val + 1) hkn
  have hcl : ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r.val + 1),
      ∑ w ∈ univ.filter (fun i : Fin n => (i : ℕ) < r.val + 1), (if G.Adj i w then 1 else 0)
        = (r.val + 1) * (r.val + 1 - 1) := by
    rw [sum_congr rfl (fun i hi => sum_row_clique G _ i hi (fun w hw hwi => ?_)), sum_const,
      hcard, smul_eq_mul]
    simp only [mem_filter, mem_univ, true_and] at hi hw
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | hi'
    · rcases lt_or_eq_of_le (Nat.le_of_lt_succ hw) with hw' | hw'
      · exact Na i w hi' hw' (fun h => hwi h.symm)
      · rw [show w = r from Fin.ext hw']; exact (N1 i hi').symm
    · rw [show i = r from Fin.ext hi']
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hw) with hw' | hw'
      · exact N1 w hw'
      · exact absurd (Fin.ext (hw'.trans hi'.symm)) hwi
  have hH : ∑ w ∈ univ.filter (fun j : Fin n => r.val + 1 ≤ (j : ℕ)), min (d w) (r.val + 1) ≤
      ∑ w ∈ univ.filter (fun j : Fin n => r.val + 1 ≤ (j : ℕ)),
        ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r.val + 1), (if G.Adj w i then 1 else 0) := by
    apply sum_le_sum
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    rcases Nb w (by omega) with hall | ⟨hnb, hsat⟩
    · rw [sum_row_eq_card]
      have : (univ.filter (fun i : Fin n => (i : ℕ) < r.val + 1)).filter (G.Adj w) =
          univ.filter (fun i : Fin n => (i : ℕ) < r.val + 1) := by
        apply filter_true_of_mem
        intro j hj
        simp only [mem_filter, mem_univ, true_and] at hj
        exact hall j (by omega)
      rw [this, hcard]
      exact min_le_right _ _
    · have : ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r.val + 1),
          (if G.Adj w i then 1 else 0) = dg G w := by
        rw [dg_eq_sum]
        apply sum_subset (subset_univ _)
        intro j _ hj
        simp only [mem_filter, mem_univ, true_and] at hj
        rw [if_neg (fun h => by have := hnb j h; omega)]
      rw [this, hsat]
      exact min_le_left _ _
  have hlt : ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r.val + 1), dg G i <
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r.val + 1), d i :=
    sum_lt_sum (fun i _ => hG i) ⟨r, by simp, hr⟩
  omega

/-! ### The two directions -/

private lemma sufficiency (d : Fin n → ℕ) (hd : Antitone d) (heven : Even (∑ i, d i))
    (hEG : EGcond d) : ∃ G : SimpleGraph (Fin n), ∀ v, dg G v = d v := by
  have main : ∀ m, m ≤ n → ∃ G : SimpleGraph (Fin n),
      (∀ v, dg G v ≤ d v) ∧ ∀ i : Fin n, i.val < m → dg G i = d i := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨⊥, fun v => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      have : dg (⊥ : SimpleGraph (Fin n)) v = 0 := by simp [dg]
      omega
    | succ m ih =>
      intro hm
      obtain ⟨G, hG, hL⟩ := ih (by omega)
      have inner : ∀ t : ℕ, ∀ G : SimpleGraph (Fin n), (∀ v, dg G v ≤ d v) →
          (∀ i : Fin n, i.val < (⟨m, by omega⟩ : Fin n).val → dg G i = d i) →
          d ⟨m, by omega⟩ - dg G ⟨m, by omega⟩ ≤ t →
          ∃ G' : SimpleGraph (Fin n), (∀ v, dg G' v ≤ d v) ∧
            ∀ i : Fin n, i.val < m + 1 → dg G' i = d i := by
        intro t
        induction t with
        | zero =>
          intro G hG hL ht
          refine ⟨G, hG, fun i hi => ?_⟩
          rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | hi'
          · exact hL i hi'
          · have e : i = ⟨m, by omega⟩ := Fin.ext hi'
            rw [e]
            have := hG ⟨m, by omega⟩
            omega
        | succ t ih2 =>
          intro G hG hL ht
          by_cases hsat : dg G ⟨m, by omega⟩ = d ⟨m, by omega⟩
          · exact ih2 G hG hL (by omega)
          · obtain ⟨G', hG'1, hG'2, hG'3⟩ :=
              improve d hd heven hEG G ⟨m, by omega⟩ hG hL (lt_of_le_of_ne (hG _) hsat)
            exact ih2 G' hG'1 hG'2 (by omega)
      exact inner _ G hG hL le_rfl
  obtain ⟨G, hG, hL⟩ := main n le_rfl
  exact ⟨G, fun v => hL v v.isLt⟩

private lemma necessity (d : Fin n → ℕ) (G : SimpleGraph (Fin n)) (hG : ∀ v, dg G v = d v) :
    Even (∑ i, d i) ∧ EGcond d := by
  have hd : d = dg G := funext fun v => (hG v).symm
  subst hd
  refine ⟨by rw [sum_dg]; exact even_two_mul _, ?_⟩
  intro k hk1 hkn
  rw [sum_split G k]
  have hcard := card_filter_lt (n := n) k hkn
  have h1 : ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k),
      ∑ w ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), (if G.Adj i w then 1 else 0)
        ≤ k * (k - 1) := by
    calc _ ≤ ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), (k - 1) :=
          sum_le_sum (fun i hi => (sum_row_le G _ i hi).trans_eq (by rw [hcard]))
      _ = k * (k - 1) := by rw [sum_const, hcard, smul_eq_mul]
  have h2 : ∑ w ∈ univ.filter (fun j : Fin n => k ≤ (j : ℕ)),
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), (if G.Adj w i then 1 else 0) ≤
        ∑ w ∈ univ.filter (fun j : Fin n => k ≤ (j : ℕ)), min (dg G w) k :=
    sum_le_sum (fun w _ => le_min (sum_row_le_dg G _ w) ((sum_row_le_card G _ w).trans_eq hcard))
  omega

end EGHelpers

theorem solution (n : ℕ) (d : Fin n → ℕ) (hd : Antitone d) :
    IsGraphic d ↔
      (Even (∑ i, d i) ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ n →
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), d i ≤
            k * (k - 1) + ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), min (d i) k) := by
  constructor
  · rintro ⟨G, hG⟩
    exact necessity d G (fun v => by have := hG v; rwa [degree_eq_dg] at this)
  · rintro ⟨heven, hEG⟩
    obtain ⟨G, hG⟩ := sufficiency d hd heven hEG
    exact ⟨G, fun v => by rw [degree_eq_dg]; exact hG v⟩
