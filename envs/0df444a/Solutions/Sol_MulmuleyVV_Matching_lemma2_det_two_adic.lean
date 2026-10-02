-- Prove2me | solution 1 for MulmuleyVV.Matching.lemma2_det_two_adic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:57:30.625861+00:00
-- url     : https://prove2.me/submissions/f5293de0-e6ec-4d08-8e23-7ba2e33a40e5

import Mathlib
import Definitions.Def_MulmuleyVV_Matching_SetSystem
import Definitions.Def_MulmuleyVV_Matching_Algorithm

set_option autoImplicit false

namespace Q53d

open Equiv Finset Function MulmuleyVV.Matching
open Equiv.Perm (sameCycle_apply_right sameCycle_apply_left sameCycle_symm_apply_right sameCycle_inv)

variable {n : ℕ}

noncomputable def cl (σ : Perm (Fin n)) (y : Fin n) : Finset (Fin n) := by
  classical exact univ.filter (fun z => σ.SameCycle y z)

theorem mem_cl {σ : Perm (Fin n)} {y z : Fin n} : z ∈ cl σ y ↔ σ.SameCycle y z := by
  classical
  unfold cl
  simp

theorem periodic (σ : Perm (Fin n)) (y : Fin n) : y ∈ periodicPts σ :=
  ⟨orderOf σ, orderOf_pos σ, by
    show (⇑σ)^[orderOf σ] y = y
    rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]; rfl⟩

theorem card_cl (σ : Perm (Fin n)) (y : Fin n) : (cl σ y).card = minimalPeriod σ y := by
  have hpos : 0 < minimalPeriod σ y := minimalPeriod_pos_of_mem_periodicPts (periodic σ y)
  have h : cl σ y = (range (minimalPeriod σ y)).image (fun k => (σ ^ k) y) := by
    ext z
    simp only [mem_cl, mem_image, mem_range]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
      refine ⟨k % minimalPeriod σ y, Nat.mod_lt _ hpos, ?_⟩
      rw [← hk, ← Equiv.Perm.iterate_eq_pow, ← Equiv.Perm.iterate_eq_pow,
        iterate_mod_minimalPeriod_eq]
    · rintro ⟨k, -, rfl⟩
      exact ⟨(k : ℤ), by simp [zpow_natCast]⟩
  rw [h, card_image_of_injOn, card_range]
  intro a ha b hb hab
  exact iterate_injOn_Iio_minimalPeriod (f := σ) (x := y) (by simpa using ha) (by simpa using hb)
    (by simpa [Equiv.Perm.iterate_eq_pow] using hab)

theorem cl_eq_of_sameCycle {σ : Perm (Fin n)} {a b : Fin n} (h : σ.SameCycle a b) :
    cl σ a = cl σ b := by
  ext z; simp only [mem_cl]; exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

noncomputable def rep (σ : Perm (Fin n)) (y : Fin n) : Fin n :=
  (cl σ y).min' ⟨y, mem_cl.2 (Perm.SameCycle.refl _ _)⟩

theorem rep_sc (σ : Perm (Fin n)) (y : Fin n) : σ.SameCycle (rep σ y) y :=
  (mem_cl.1 (min'_mem _ _)).symm

theorem min'_congr' {s t : Finset (Fin n)} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by subst h; rfl

theorem rep_eq {σ : Perm (Fin n)} {a b : Fin n} (h : σ.SameCycle a b) : rep σ a = rep σ b :=
  min'_congr' (cl_eq_of_sameCycle h) _ _

noncomputable def colA (σ : Perm (Fin n)) : Finset (Fin n) := by
  classical exact univ.filter (fun y => ∃ t : ℕ, Even t ∧ (σ ^ t) (rep σ y) = y)

theorem mem_colA {σ : Perm (Fin n)} {y : Fin n} :
    y ∈ colA σ ↔ ∃ t : ℕ, Even t ∧ (σ ^ t) (rep σ y) = y := by
  classical
  unfold colA
  simp

theorem parity_of_eq (σ : Perm (Fin n)) (r : Fin n) (h : Even (minimalPeriod σ r)) {t s : ℕ}
    (hts : (σ ^ t) r = (σ ^ s) r) : (Even t ↔ Even s) := by
  wlog hle : s ≤ t generalizing t s
  · exact (this hts.symm (by omega)).symm
  have hper : IsPeriodicPt σ (t - s) ((σ ^ s) r) := by
    show (⇑σ)^[t - s] ((σ ^ s) r) = (σ ^ s) r
    rw [Equiv.Perm.iterate_eq_pow, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hle, hts]
  have hd := hper.minimalPeriod_dvd
  rw [← Equiv.Perm.iterate_eq_pow, minimalPeriod_apply_iterate (periodic σ r)] at hd
  have h2 : Even (t - s) := even_iff_two_dvd.2 (dvd_trans (even_iff_two_dvd.1 h) hd)
  simp only [Nat.even_iff] at *
  omega

theorem colA_iff (σ : Perm (Fin n)) (y : Fin n) (hev : Even (cl σ y).card) :
    (y ∈ colA σ ↔ σ y ∉ colA σ) := by
  have hr : rep σ (σ y) = rep σ y :=
    rep_eq ((sameCycle_apply_left).2 (Perm.SameCycle.refl σ y))
  have hmp : Even (minimalPeriod σ (rep σ y)) := by
    rw [← card_cl, cl_eq_of_sameCycle (rep_sc σ y)]; exact hev
  obtain ⟨t0, ht0⟩ := (rep_sc σ y).exists_nat_pow_eq
  rw [mem_colA, mem_colA, hr]
  constructor
  · rintro ⟨t, ht, hty⟩ ⟨s, hs, hsy⟩
    have : (σ ^ (t + 1)) (rep σ y) = (σ ^ s) (rep σ y) := by
      rw [hsy, pow_succ', Perm.mul_apply, hty]
    have := (parity_of_eq σ _ hmp this).2 hs
    rw [Nat.even_add_one] at this
    exact this ht
  · intro hn
    rcases Nat.even_or_odd t0 with he | ho
    · exact ⟨t0, he, ht0⟩
    · exfalso
      apply hn
      refine ⟨t0 + 1, ho.add_one, ?_⟩
      rw [pow_succ', Perm.mul_apply, ht0]

theorem even_card_of (σ : Perm (Fin n)) (S : Finset (Fin n)) (hS : ∀ y, σ y ∈ S ↔ y ∈ S)
    (hev : ∀ y ∈ S, Even (cl σ y).card) : Even S.card := by
  classical
  have h1 : (S.filter (· ∈ colA σ)).card = (S.filter (· ∉ colA σ)).card := by
    apply card_nbij' (fun y => σ y) (fun y => σ⁻¹ y)
    · intro a ha
      simp only [coe_filter, Set.mem_setOf_eq] at ha ⊢
      exact ⟨(hS a).2 ha.1, (colA_iff σ a (hev a ha.1)).1 ha.2⟩
    · intro a ha
      simp only [coe_filter, Set.mem_setOf_eq] at ha ⊢
      have h1 : σ⁻¹ a ∈ S := by rw [← hS]; simpa using ha.1
      refine ⟨h1, ?_⟩
      rw [colA_iff σ _ (hev _ h1)]
      simpa using ha.2
    · intro a _; simp
    · intro a _; simp
  rw [← card_filter_add_card_filter_not (fun y => y ∈ colA σ), h1]
  exact ⟨_, rfl⟩

/-! ### cycle reversal -/

theorem sc_inv_right {σ : Perm (Fin n)} {x y : Fin n} :
    σ.SameCycle x (σ⁻¹ y) ↔ σ.SameCycle x y := sameCycle_symm_apply_right

noncomputable def rev (σ : Perm (Fin n)) (x : Fin n) : Perm (Fin n) := by
  classical exact
  { toFun := fun y => if σ.SameCycle x y then σ⁻¹ y else σ y
    invFun := fun y => if σ.SameCycle x y then σ y else σ⁻¹ y
    left_inv := fun y => by
      by_cases h : σ.SameCycle x y
      · have h' : σ.SameCycle x (σ⁻¹ y) := sc_inv_right.2 h
        simp [h, h']
      · have h' : ¬ σ.SameCycle x (σ y) := by rwa [sameCycle_apply_right]
        simp [h, h']
    right_inv := fun y => by
      by_cases h : σ.SameCycle x y
      · have h' : σ.SameCycle x (σ y) := sameCycle_apply_right.2 h
        simp [h, h']
      · have h' : ¬ σ.SameCycle x (σ⁻¹ y) := by rwa [sc_inv_right]
        simp [h, h'] }

theorem rev_apply_pos {σ : Perm (Fin n)} {x y : Fin n} (h : σ.SameCycle x y) :
    rev σ x y = σ⁻¹ y := by
  classical
  unfold rev
  simp [h]

theorem rev_apply_neg {σ : Perm (Fin n)} {x y : Fin n} (h : ¬ σ.SameCycle x y) :
    rev σ x y = σ y := by
  classical
  unfold rev
  simp [h]

theorem sc_mono {σ τ : Perm (Fin n)} (h : ∀ y, τ.SameCycle y (σ y)) {a b : Fin n}
    (hab : σ.SameCycle a b) : τ.SameCycle a b := by
  obtain ⟨k, rfl⟩ := hab.exists_nat_pow_eq
  clear hab
  induction k with
  | zero => simpa using Perm.SameCycle.refl τ a
  | succ k ih => rw [pow_succ', Perm.mul_apply]; exact ih.trans (h _)

theorem rev_sc (σ : Perm (Fin n)) (x : Fin n) {a b : Fin n} :
    (rev σ x).SameCycle a b ↔ σ.SameCycle a b := by
  constructor
  · apply sc_mono
    intro y
    by_cases h : σ.SameCycle x y
    · rw [rev_apply_pos h]; exact sc_inv_right.2 (Perm.SameCycle.refl _ _)
    · rw [rev_apply_neg h]; exact sameCycle_apply_right.2 (Perm.SameCycle.refl _ _)
  · apply sc_mono
    intro y
    by_cases h : σ.SameCycle x y
    · have h2 : rev σ x (σ y) = y := by
        rw [rev_apply_pos (sameCycle_apply_right.2 h)]; simp
      apply sameCycle_apply_right.1
      rw [h2]
    · rw [← rev_apply_neg h]; exact sameCycle_apply_right.2 (Perm.SameCycle.refl _ _)

theorem cl_rev (σ : Perm (Fin n)) (x y : Fin n) : cl (rev σ x) y = cl σ y := by
  ext z; simp only [mem_cl, rev_sc]

theorem rev_rev (σ : Perm (Fin n)) (x : Fin n) : rev (rev σ x) x = σ := by
  refine Equiv.ext fun y => ?_
  by_cases h : σ.SameCycle x y
  · rw [rev_apply_pos ((rev_sc σ x).2 h)]
    rw [Perm.inv_eq_iff_eq, rev_apply_pos (sameCycle_apply_right.2 h)]
    simp
  · rw [rev_apply_neg (by rwa [rev_sc]), rev_apply_neg h]

theorem rev_eq_mul (σ : Perm (Fin n)) (x : Fin n) :
    ∃ c : Perm (Fin n), rev σ x = σ * (c * c) := by
  classical
  refine ⟨(σ.cycleOf x)⁻¹, ?_⟩
  refine Equiv.ext fun y => ?_
  rw [Perm.cycleOf_inv]
  simp only [Perm.mul_apply, Perm.cycleOf_apply, sameCycle_inv]
  by_cases h : σ.SameCycle x y
  · have h' : σ.SameCycle x (σ⁻¹ y) := sc_inv_right.2 h
    rw [rev_apply_pos h, if_pos h, if_pos h']
    simp
  · rw [rev_apply_neg h, if_neg h, if_neg h]

theorem sign_rev (σ : Perm (Fin n)) (x : Fin n) : Perm.sign (rev σ x) = Perm.sign σ := by
  obtain ⟨c, hc⟩ := rev_eq_mul σ x
  rw [hc, Perm.sign_mul, Perm.sign_mul, Int.units_mul_self, mul_one]

/-- product of a permutation's entries (Leibniz convention `M (σ k) k`) -/
def prodB (B : Matrix (Fin n) (Fin n) ℤ) (σ : Perm (Fin n)) : ℤ := ∏ k, B (σ k) k

def term (B : Matrix (Fin n) (Fin n) ℤ) (σ : Perm (Fin n)) : ℤ :=
  ((Perm.sign σ : ℤˣ) : ℤ) * prodB B σ

theorem prodB_rev (B : Matrix (Fin n) (Fin n) ℤ) (hskew : ∀ a b, B a b = - B b a)
    (σ : Perm (Fin n)) (x : Fin n) (hodd : Odd (cl σ x).card) :
    prodB B (rev σ x) = - prodB B σ := by
  classical
  unfold prodB
  rw [← prod_mul_prod_compl (cl σ x), ← prod_mul_prod_compl (cl σ x) (fun k => B (σ k) k)]
  have h2 : ∏ k ∈ (cl σ x)ᶜ, B (rev σ x k) k = ∏ k ∈ (cl σ x)ᶜ, B (σ k) k := by
    apply prod_congr rfl
    intro k hk
    rw [mem_compl, mem_cl] at hk
    rw [rev_apply_neg hk]
  have h1 : ∏ k ∈ cl σ x, B (rev σ x k) k = ∏ k ∈ cl σ x, B k (σ k) := by
    apply prod_nbij' (fun k => σ⁻¹ k) (fun k => σ k)
    · intro a ha
      simp only [mem_coe, mem_cl] at ha ⊢
      exact sc_inv_right.2 ha
    · intro a ha
      simp only [mem_coe, mem_cl] at ha ⊢
      exact sameCycle_apply_right.2 ha
    · intro a _; simp
    · intro a _; simp
    · intro a ha
      rw [mem_cl] at ha
      rw [rev_apply_pos ha]
      simp
  have h3 : ∏ k ∈ cl σ x, B k (σ k) = - ∏ k ∈ cl σ x, B (σ k) k := by
    rw [prod_congr rfl (fun k _ => hskew k (σ k)), prod_neg, hodd.neg_one_pow]
    ring
  rw [h1, h2, h3]
  ring

theorem term_rev (B : Matrix (Fin n) (Fin n) ℤ) (hskew : ∀ a b, B a b = - B b a)
    (σ : Perm (Fin n)) (x : Fin n) (hodd : Odd (cl σ x).card) :
    term B (rev σ x) = - term B σ := by
  unfold term
  rw [sign_rev, prodB_rev B hskew σ x hodd]
  ring

/-- odd cycles avoiding the cycle of `i` -/
noncomputable def oddX (i : Fin n) (σ : Perm (Fin n)) : Finset (Fin n) := by
  classical exact univ.filter (fun y => Odd (cl σ y).card ∧ ¬ σ.SameCycle i y)

theorem mem_oddX {i : Fin n} {σ : Perm (Fin n)} {y : Fin n} :
    y ∈ oddX i σ ↔ Odd (cl σ y).card ∧ ¬ σ.SameCycle i y := by
  classical
  unfold oddX
  simp

theorem oddX_rev (i : Fin n) (σ : Perm (Fin n)) (x : Fin n) : oddX i (rev σ x) = oddX i σ := by
  ext y; simp only [mem_oddX, cl_rev, rev_sc]

noncomputable def iota (i : Fin n) (σ : Perm (Fin n)) : Perm (Fin n) :=
  if h : (oddX i σ).Nonempty then rev σ ((oddX i σ).min' h) else σ

theorem sum_odd_zero (B : Matrix (Fin n) (Fin n) ℤ) (hskew : ∀ a b, B a b = - B b a)
    (hdiag : ∀ a, B a a = 0) (i j : Fin n) :
    ∑ σ ∈ (univ.filter (fun σ : Perm (Fin n) => σ j = i)).filter
      (fun σ => (oddX i σ).Nonempty), term B σ = 0 := by
  classical
  refine sum_involution (fun σ _ => iota i σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    have hx := min'_mem _ hσ.2
    rw [mem_oddX] at hx
    simp only [iota, dif_pos hσ.2]
    rw [term_rev B hskew σ _ hx.1]
    ring
  · intro σ hσ hne heq
    simp only [mem_filter, mem_univ, true_and] at hσ
    have hx := min'_mem _ hσ.2
    rw [mem_oddX] at hx
    simp only [iota, dif_pos hσ.2] at heq
    set x := (oddX i σ).min' hσ.2
    have h1 : rev σ x x = σ x := by rw [heq]
    rw [rev_apply_pos (Perm.SameCycle.refl _ _)] at h1
    have hper : IsPeriodicPt σ 2 x := by
      show (⇑σ)^[2] x = x
      simp only [iterate_succ, iterate_zero, comp_apply, id]
      rw [← h1]; simp
    have hd := hper.minimalPeriod_dvd
    rw [← card_cl] at hd
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · rw [card_cl, minimalPeriod_eq_one_iff_isFixedPt] at h
      apply hne
      unfold term prodB
      rw [prod_eq_zero (mem_univ x) (by rw [h.eq, hdiag]), mul_zero]
    · rw [h] at hx; exact (Nat.not_even_iff_odd.2 hx.1) even_two
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    have hx := min'_mem _ hσ.2
    rw [mem_oddX] at hx
    simp only [iota, dif_pos hσ.2]
    refine ⟨?_, by rw [oddX_rev]; exact hσ.2⟩
    generalize (oddX i σ).min' hσ.2 = x at hx ⊢
    obtain ⟨hji, -⟩ := hσ
    have hj : ¬ σ.SameCycle x j := by
      intro h
      apply hx.2
      have := (sameCycle_apply_right.2 h)
      rw [hji] at this
      exact this.symm
    rw [rev_apply_neg hj, hji]
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    have hne : (oddX i (rev σ ((oddX i σ).min' hσ.2))).Nonempty := by rw [oddX_rev]; exact hσ.2
    simp only [iota, dif_pos hσ.2, dif_pos hne]
    rw [min'_congr' (oddX_rev i σ _) hne hσ.2, rev_rev]

/-! ### the weighted Tutte matrix -/

def wv (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : G.edgeSet → ℕ) (a b : Fin n) : ℕ :=
  if h : G.Adj a b then w ⟨s(a, b), G.mem_edgeSet.mpr h⟩ else 0

theorem wv_symm (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : G.edgeSet → ℕ) (a b : Fin n) :
    wv G w a b = wv G w b a := by
  unfold wv
  by_cases h : G.Adj a b
  · rw [dif_pos h, dif_pos h.symm]
    exact congrArg w (Subtype.ext Sym2.eq_swap)
  · rw [dif_neg h, dif_neg (fun h' => h h'.symm)]

theorem B_apply (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : G.edgeSet → ℕ) (a b : Fin n) :
    weightedTutteMatrix G w a b =
      if G.Adj a b then (if a < b then (2:ℤ) ^ (wv G w a b) else -(2:ℤ) ^ (wv G w a b)) else 0 := by
  by_cases h : G.Adj a b
  · simp only [weightedTutteMatrix, wv, dif_pos h, if_pos h]
  · simp only [weightedTutteMatrix, dif_neg h, if_neg h]

theorem B_skew (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : G.edgeSet → ℕ) (a b : Fin n) :
    weightedTutteMatrix G w a b = - weightedTutteMatrix G w b a := by
  rw [B_apply, B_apply, wv_symm G w b a]
  by_cases h : G.Adj a b
  · rw [if_pos h, if_pos h.symm]
    rcases lt_or_gt_of_ne (G.ne_of_adj h) with hl | hl
    · rw [if_pos hl, if_neg (not_lt.2 hl.le)]; try ring
    · rw [if_neg (not_lt.2 hl.le), if_pos hl]; try ring
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]; try ring

theorem B_diag (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : G.edgeSet → ℕ) (a : Fin n) :
    weightedTutteMatrix G w a a = 0 := by
  rw [B_apply, if_neg (G.irrefl)]

theorem B_natAbs (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : G.edgeSet → ℕ) (a b : Fin n) :
    (weightedTutteMatrix G w a b).natAbs = if G.Adj a b then 2 ^ (wv G w a b) else 0 := by
  rw [B_apply]
  split_ifs <;> simp [Int.natAbs_pow]

theorem prodB_natAbs (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : G.edgeSet → ℕ)
    (σ : Perm (Fin n)) (hσ : ∀ k, G.Adj (σ k) k) :
    (prodB (weightedTutteMatrix G w) σ).natAbs = 2 ^ (∑ k, wv G w (σ k) k) := by
  unfold prodB
  rw [← prod_pow_eq_pow_sum]
  have := map_prod Int.natAbsHom (fun k => weightedTutteMatrix G w (σ k) k) univ
  simp only [Int.natAbsHom_apply] at this
  rw [this]
  apply prod_congr rfl
  intro k _
  rw [B_natAbs, if_pos (hσ k)]

theorem term_natAbs (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : G.edgeSet → ℕ)
    (σ : Perm (Fin n)) (hσ : ∀ k, G.Adj (σ k) k) :
    (term (weightedTutteMatrix G w) σ).natAbs = 2 ^ (∑ k, wv G w (σ k) k) := by
  unfold term
  rw [Int.natAbs_mul, prodB_natAbs G w σ hσ]
  simp

theorem term_eq_zero (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : G.edgeSet → ℕ)
    (σ : Perm (Fin n)) (hσ : ¬ ∀ k, G.Adj (σ k) k) :
    term (weightedTutteMatrix G w) σ = 0 := by
  push_neg at hσ
  obtain ⟨k, hk⟩ := hσ
  unfold term prodB
  rw [prod_eq_zero (mem_univ k) (by rw [B_apply, if_neg hk]), mul_zero]

/-! ### perfect matchings from a 2-colouring -/

def fe {G : SimpleGraph (Fin n)} (σ : Perm (Fin n)) (hσ : ∀ k, G.Adj (σ k) k) (k : Fin n) :
    G.edgeSet :=
  ⟨s(k, σ k), G.mem_edgeSet.mpr (hσ k).symm⟩

theorem pm_of_col {G : SimpleGraph (Fin n)} (σ : Perm (Fin n)) (hσ : ∀ k, G.Adj (σ k) k)
    (T : Finset (Fin n)) (hT : ∀ k, k ∈ T ↔ σ k ∉ T) :
    IsPerfectMatchingEdges G (T.image (fe σ hσ)) := by
  intro v
  have key : ∀ k ∈ T, v ∈ (fe σ hσ k : Sym2 (Fin n)) → k = (if v ∈ T then v else σ⁻¹ v) := by
    intro k hk hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · rw [if_pos hk]
    · rw [if_neg ((hT k).1 hk)]; simp
  by_cases hvT : v ∈ T
  · refine ⟨fe σ hσ v, ⟨mem_image_of_mem _ hvT, Sym2.mem_mk_left _ _⟩, ?_⟩
    rintro e ⟨he, hve⟩
    obtain ⟨k, hk, rfl⟩ := mem_image.1 he
    have := key k hk hve
    rw [if_pos hvT] at this
    rw [this]
  · have hk : σ⁻¹ v ∈ T := by rw [hT]; simpa using hvT
    refine ⟨fe σ hσ (σ⁻¹ v), ⟨mem_image_of_mem _ hk, ?_⟩, ?_⟩
    · show v ∈ s(σ⁻¹ v, σ (σ⁻¹ v))
      simp
    · rintro e ⟨he, hve⟩
      obtain ⟨k, hk', rfl⟩ := mem_image.1 he
      have := key k hk' hve
      rw [if_neg hvT] at this
      rw [this]

theorem sw_col {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (w : G.edgeSet → ℕ)
    (σ : Perm (Fin n)) (hσ : ∀ k, G.Adj (σ k) k)
    (T : Finset (Fin n)) (hT : ∀ k, k ∈ T ↔ σ k ∉ T) :
    setWeight w (T.image (fe σ hσ)) = ∑ k ∈ T, wv G w k (σ k) := by
  unfold setWeight
  rw [sum_image]
  · apply sum_congr rfl
    intro k _
    unfold wv
    rw [dif_pos (hσ k).symm]
    rfl
  · intro a ha b hb hab
    have h := congrArg Subtype.val hab
    simp only [fe] at h
    rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exfalso
      have := (hT b).1 hb
      rw [← h1] at this
      exact this ha

theorem two_pm {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (w : G.edgeSet → ℕ)
    (σ : Perm (Fin n)) (hσ : ∀ k, G.Adj (σ k) k) (hev : ∀ y, Even (cl σ y).card) :
    IsPerfectMatchingEdges G ((colA σ).image (fe σ hσ)) ∧
    IsPerfectMatchingEdges G ((colA σ)ᶜ.image (fe σ hσ)) ∧
    ∑ k, wv G w (σ k) k = setWeight w ((colA σ).image (fe σ hσ)) +
      setWeight w ((colA σ)ᶜ.image (fe σ hσ)) := by
  have hA : ∀ k, k ∈ colA σ ↔ σ k ∉ colA σ := fun k => colA_iff σ k (hev k)
  have hAc : ∀ k, k ∈ (colA σ)ᶜ ↔ σ k ∉ (colA σ)ᶜ := by
    intro k
    simp only [mem_compl, not_not]
    rw [hA k, not_not]
  refine ⟨pm_of_col σ hσ _ hA, pm_of_col σ hσ _ hAc, ?_⟩
  rw [sw_col w σ hσ _ hA, sw_col w σ hσ _ hAc, sum_add_sum_compl]
  exact sum_congr rfl (fun k _ => wv_symm G w (σ k) k)

theorem pm_eq_of_subset {G : SimpleGraph (Fin n)} {M M' : Finset G.edgeSet}
    (hM : IsPerfectMatchingEdges G M) (hM' : IsPerfectMatchingEdges G M') (h : M ⊆ M') :
    M = M' := by
  refine Finset.Subset.antisymm h (fun e he => ?_)
  obtain ⟨v, hv⟩ : ∃ v, v ∈ (e : Sym2 (Fin n)) := by
    obtain ⟨x, hx⟩ := e
    induction x using Sym2.ind with
    | h a b => exact ⟨a, Sym2.mem_mk_left _ _⟩
  obtain ⟨e1, ⟨he1, hv1⟩, -⟩ := hM v
  have : e1 = e := (hM' v).unique ⟨h he1, hv1⟩ ⟨he, hv⟩
  rw [← this]; exact he1

/-! ### the partner permutation of a perfect matching -/

noncomputable def pe {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) (v : Fin n) : G.edgeSet :=
  (hM0 v).exists.choose

theorem pe_spec {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) (v : Fin n) :
    pe hM0 v ∈ M0 ∧ v ∈ (pe hM0 v : Sym2 (Fin n)) :=
  (hM0 v).exists.choose_spec

noncomputable def pf {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) (v : Fin n) : Fin n :=
  Sym2.Mem.other (pe_spec hM0 v).2

theorem pf_edge {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) (v : Fin n) :
    (pe hM0 v : Sym2 (Fin n)) = s(v, pf hM0 v) :=
  (Sym2.other_spec (pe_spec hM0 v).2).symm

theorem pf_unique {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) {v u : Fin n} {e : G.edgeSet} (he : e ∈ M0)
    (heq : (e : Sym2 (Fin n)) = s(v, u)) : pf hM0 v = u := by
  have h1 : e = pe hM0 v :=
    (hM0 v).unique ⟨he, by rw [heq]; exact Sym2.mem_mk_left _ _⟩ (pe_spec hM0 v)
  have h2 : s(v, pf hM0 v) = s(v, u) := by rw [← pf_edge, ← h1, heq]
  exact Sym2.congr_right.1 h2

theorem pf_adj {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) (v : Fin n) : G.Adj v (pf hM0 v) := by
  have := (pe hM0 v).2
  rw [pf_edge] at this
  exact G.mem_edgeSet.1 this

theorem pf_invol {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) (v : Fin n) : pf hM0 (pf hM0 v) = v :=
  pf_unique hM0 (pe_spec hM0 v).1 (by rw [pf_edge]; exact Sym2.eq_swap)

noncomputable def pperm {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) : Perm (Fin n) :=
  Function.Involutive.toPerm (pf hM0) (pf_invol hM0)

theorem pperm_apply {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) (v : Fin n) : pperm hM0 v = pf hM0 v := rfl

theorem pperm_adj {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) (k : Fin n) : G.Adj (pperm hM0 k) k :=
  (pf_adj hM0 k).symm

theorem pperm_even {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) (y : Fin n) : Even (cl (pperm hM0) y).card := by
  rw [card_cl]
  have hper : IsPeriodicPt (pperm hM0) 2 y := by
    show (⇑(pperm hM0))^[2] y = y
    simp only [iterate_succ, iterate_zero, comp_apply, id]
    rw [pperm_apply, pperm_apply, pf_invol]
  rcases (Nat.dvd_prime Nat.prime_two).1 hper.minimalPeriod_dvd with h | h
  · exfalso
    rw [minimalPeriod_eq_one_iff_isFixedPt] at h
    exact G.ne_of_adj (pf_adj hM0 y) h.symm
  · rw [h]; exact even_two

theorem n_even {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) : Even n := by
  have := even_card_of (pperm hM0) univ (by simp) (fun y _ => pperm_even hM0 y)
  rwa [card_univ, Fintype.card_fin] at this

theorem pperm_iff {G : SimpleGraph (Fin n)} {M0 : Finset G.edgeSet}
    (hM0 : IsPerfectMatchingEdges G M0) (i j : Fin n) : pperm hM0 j = i ↔ j = pperm hM0 i := by
  constructor
  · rintro rfl; exact (pf_invol hM0 j).symm
  · rintro rfl; exact pf_invol hM0 i

/-! ### weights -/

theorem wt_gt {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (w : G.edgeSet → ℕ)
    {M0 : Finset G.edgeSet} (hM0 : IsPerfectMatchingEdges G M0)
    (huniq : ∀ M, IsPerfectMatchingEdges G M → M ≠ M0 → setWeight w M0 < setWeight w M)
    (σ : Perm (Fin n)) (hσ : ∀ k, G.Adj (σ k) k) (hev : ∀ y, Even (cl σ y).card)
    (hne : σ ≠ pperm hM0) : 2 * setWeight w M0 + 1 ≤ ∑ k, wv G w (σ k) k := by
  obtain ⟨h1, h2, hsum⟩ := two_pm w σ hσ hev
  have hge : ∀ M, IsPerfectMatchingEdges G M → setWeight w M0 ≤ setWeight w M := by
    intro M hM
    by_cases h : M = M0
    · rw [h]
    · exact (huniq M hM h).le
  rw [hsum]
  by_contra hlt
  push_neg at hlt
  have e1 : (colA σ).image (fe σ hσ) = M0 := by
    by_contra h
    have := huniq _ h1 h
    have := hge _ h2
    omega
  have e2 : (colA σ)ᶜ.image (fe σ hσ) = M0 := by
    by_contra h
    have := huniq _ h2 h
    have := hge _ h1
    omega
  apply hne
  refine Equiv.ext fun k => ?_
  have hk : fe σ hσ k ∈ M0 := by
    by_cases hkA : k ∈ colA σ
    · rw [← e1]; exact mem_image_of_mem _ hkA
    · rw [← e2]; exact mem_image_of_mem _ (mem_compl.2 hkA)
  exact (pf_unique hM0 hk rfl).symm

theorem wt_p {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (w : G.edgeSet → ℕ)
    {M0 : Finset G.edgeSet} (hM0 : IsPerfectMatchingEdges G M0) :
    ∑ k, wv G w (pperm hM0 k) k = 2 * setWeight w M0 := by
  obtain ⟨h1, h2, hsum⟩ := two_pm w (pperm hM0) (pperm_adj hM0) (pperm_even hM0)
  have sub : ∀ T : Finset (Fin n), T.image (fe (pperm hM0) (pperm_adj hM0)) ⊆ M0 := by
    intro T e he
    obtain ⟨k, -, rfl⟩ := mem_image.1 he
    have : fe (pperm hM0) (pperm_adj hM0) k = pe hM0 k := Subtype.ext (pf_edge hM0 k).symm
    rw [this]; exact (pe_spec hM0 k).1
  rw [hsum, pm_eq_of_subset h1 hM0 (sub _), pm_eq_of_subset h2 hM0 (sub _)]; ring

/-! ### the key congruence -/

theorem key {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (w : G.edgeSet → ℕ)
    {M0 : Finset G.edgeSet} (hM0 : IsPerfectMatchingEdges G M0)
    (huniq : ∀ M, IsPerfectMatchingEdges G M → M ≠ M0 → setWeight w M0 < setWeight w M)
    (i j : Fin n) :
    (2:ℤ) ^ (2 * setWeight w M0 + 1) ∣
      (∑ σ ∈ univ.filter (fun σ : Perm (Fin n) => σ j = i), term (weightedTutteMatrix G w) σ) -
        (if pperm hM0 j = i then term (weightedTutteMatrix G w) (pperm hM0) else 0) := by
  rw [← sum_filter_add_sum_filter_not (univ.filter (fun σ : Perm (Fin n) => σ j = i))
    (fun σ => (oddX i σ).Nonempty),
    sum_odd_zero (weightedTutteMatrix G w) (B_skew G w) (B_diag G w) i j, zero_add]
  have hdiv : ∀ σ ∈ (univ.filter (fun σ : Perm (Fin n) => σ j = i)).filter
      (fun σ => ¬ (oddX i σ).Nonempty),
      σ ≠ pperm hM0 → (2:ℤ) ^ (2 * setWeight w M0 + 1) ∣ term (weightedTutteMatrix G w) σ := by
    intro σ hσm hne
    simp only [mem_filter, mem_univ, true_and] at hσm
    by_cases hσ : ∀ k, G.Adj (σ k) k
    · have hS : ∀ y, ¬ σ.SameCycle i y → Even (cl σ y).card := by
        intro y hy
        by_contra hodd
        rw [Nat.not_even_iff_odd] at hodd
        exact hσm.2 ⟨y, mem_oddX.2 ⟨hodd, hy⟩⟩
      classical
      have hSeven : Even (univ.filter (fun y => ¬ σ.SameCycle i y)).card :=
        even_card_of σ _ (by intro y; simp [sameCycle_apply_right])
          (fun y hy => hS y (by simpa using hy))
      have hci : Even (cl σ i).card := by
        have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
          (fun y => σ.SameCycle i y)
        rw [card_univ, Fintype.card_fin] at h
        have hcl : cl σ i = univ.filter (fun y => σ.SameCycle i y) := by
          ext y; simp [mem_cl]
        rw [hcl]
        have hn := n_even hM0
        rw [← h] at hn
        exact (Nat.even_add.1 hn).2 hSeven
      have hev : ∀ y, Even (cl σ y).card := by
        intro y
        by_cases hy : σ.SameCycle i y
        · rw [← cl_eq_of_sameCycle hy]; exact hci
        · exact hS y hy
      have hw := wt_gt w hM0 huniq σ hσ hev hne
      rw [← Int.natAbs_dvd_natAbs, term_natAbs G w σ hσ]
      have h2 : ((2:ℤ) ^ (2 * setWeight w M0 + 1)).natAbs = 2 ^ (2 * setWeight w M0 + 1) := by
        simp
      rw [h2]
      exact Nat.pow_dvd_pow 2 hw
    · rw [term_eq_zero G w σ hσ]; exact dvd_zero _
  by_cases hpj : pperm hM0 j = i
  · have hpE : pperm hM0 ∈ (univ.filter (fun σ : Perm (Fin n) => σ j = i)).filter
        (fun σ => ¬ (oddX i σ).Nonempty) := by
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨hpj, ?_⟩
      rintro ⟨y, hy⟩
      rw [mem_oddX] at hy
      exact (Nat.not_even_iff_odd.2 hy.1) (pperm_even hM0 y)
    rw [if_pos hpj, ← add_sum_erase _ _ hpE, add_sub_cancel_left]
    exact dvd_sum (fun σ hσ => hdiv σ (mem_of_mem_erase hσ) (ne_of_mem_erase hσ))
  · rw [if_neg hpj, sub_zero]
    refine dvd_sum (fun σ hσ => hdiv σ hσ ?_)
    rintro rfl
    simp only [mem_filter, mem_univ, true_and] at hσ
    exact hpj hσ.1

/-! ### Leibniz / Laplace -/

theorem adj_mul (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    A.adjugate j i * A i j = ∑ σ ∈ univ.filter (fun σ : Perm (Fin n) => σ j = i), term A σ := by
  rw [Matrix.adjugate_apply, Matrix.det_apply', sum_mul, sum_filter]
  apply sum_congr rfl
  intro σ _
  unfold term prodB
  by_cases h : σ j = i
  · rw [if_pos h]
    have hprod : ∏ k, (A.updateRow i (Pi.single j 1)) (σ k) k = ∏ k ∈ univ.erase j, A (σ k) k := by
      rw [← mul_prod_erase univ _ (mem_univ j), Matrix.updateRow_apply, if_pos h,
        Pi.single_eq_same, one_mul]
      apply prod_congr rfl
      intro k hk
      have hkj : k ≠ j := ne_of_mem_erase hk
      have : σ k ≠ i := by rw [← h]; exact σ.injective.ne hkj
      rw [Matrix.updateRow_apply, if_neg this]
    rw [hprod, ← mul_prod_erase univ (fun k => A (σ k) k) (mem_univ j), h]
    push_cast
    ring
  · rw [if_neg h]
    have hk : σ (σ⁻¹ i) = i := by simp
    have hne : σ⁻¹ i ≠ j := fun h' => h (by rw [← h']; simp)
    rw [prod_eq_zero (mem_univ (σ⁻¹ i))
      (by rw [Matrix.updateRow_apply, if_pos hk, Pi.single_eq_of_ne hne]), mul_zero, zero_mul]

theorem det_eq_sum (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    A.det = ∑ j, A.adjugate j i * A i j := by
  have := congrFun (congrFun (Matrix.mul_adjugate A) i) i
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
  rw [← this]
  exact sum_congr rfl (fun j _ => mul_comm _ _)

theorem det_cong {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (w : G.edgeSet → ℕ)
    {M0 : Finset G.edgeSet} (hM0 : IsPerfectMatchingEdges G M0)
    (huniq : ∀ M, IsPerfectMatchingEdges G M → M ≠ M0 → setWeight w M0 < setWeight w M)
    (i : Fin n) :
    (2:ℤ) ^ (2 * setWeight w M0 + 1) ∣
      (weightedTutteMatrix G w).det - term (weightedTutteMatrix G w) (pperm hM0) := by
  rw [det_eq_sum _ i]
  have h1 : ∑ j, (if pperm hM0 j = i then term (weightedTutteMatrix G w) (pperm hM0) else 0) =
      term (weightedTutteMatrix G w) (pperm hM0) := by
    simp only [pperm_iff hM0 i]
    rw [sum_ite_eq']
    simp
  rw [← h1, ← sum_sub_distrib]
  exact dvd_sum (fun j _ => by rw [adj_mul]; exact key w hM0 huniq i j)

/-! ### 2-adic bookkeeping -/

theorem two_pow_form (T : ℤ) (W : ℕ) (hT : T.natAbs = 2 ^ (2 * W)) :
    T = 2 ^ (2 * W) ∨ T = -2 ^ (2 * W) := by
  rcases Int.natAbs_eq T with h | h
  · left; rw [h, hT]; push_cast; ring
  · right; rw [h, hT]; push_cast; ring

theorem padic_of (D T : ℤ) (W : ℕ) (hT : T = 2 ^ (2 * W) ∨ T = -2 ^ (2 * W))
    (h : (2:ℤ) ^ (2 * W + 1) ∣ D - T) : padicValInt 2 D = 2 * W := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨u, hu, hD⟩ : ∃ u : ℤ, (u = 1 + 2 * q ∨ u = -1 + 2 * q) ∧ D = 2 ^ (2 * W) * u := by
    rcases hT with rfl | rfl
    · exact ⟨1 + 2 * q, Or.inl rfl, by rw [pow_succ] at hq; linear_combination hq⟩
    · exact ⟨-1 + 2 * q, Or.inr rfl, by rw [pow_succ] at hq; linear_combination hq⟩
  have hu0 : u ≠ 0 := by rcases hu with rfl | rfl <;> omega
  have hD0 : D ≠ 0 := by rw [hD]; exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hu0
  have h1 : 2 * W ≤ padicValInt 2 D := by
    have := (padicValInt_dvd_iff (p := 2) (2 * W) D).1 ⟨u, by rw [hD]; push_cast; ring⟩
    rcases this with h | h
    · exact absurd h hD0
    · exact h
  have h2 : ¬ (2 * W + 1 ≤ padicValInt 2 D) := by
    intro hle
    obtain ⟨r, hr⟩ := (padicValInt_dvd_iff (p := 2) (2 * W + 1) D).2 (Or.inr hle)
    rw [hD] at hr
    push_cast at hr
    have hur : u = 2 * r := by
      have h2W : (2:ℤ) ^ (2 * W) ≠ 0 := pow_ne_zero _ two_ne_zero
      apply mul_left_cancel₀ h2W
      rw [hr]; ring
    rcases hu with rfl | rfl <;> omega
  omega

theorem oddquot_iff (S T : ℤ) (W : ℕ) (hT : T = 2 ^ (2 * W) ∨ T = -2 ^ (2 * W)) (b : Prop)
    [Decidable b] (h : (2:ℤ) ^ (2 * W + 1) ∣ S - (if b then T else 0)) :
    OddQuot S (2 * W) ↔ b := by
  obtain ⟨q, hq⟩ := h
  have h2W : (2:ℤ) ^ (2 * W) ≠ 0 := pow_ne_zero _ two_ne_zero
  by_cases hb : b
  · rw [if_pos hb] at hq
    refine ⟨fun _ => hb, fun _ => ?_⟩
    rcases hT with rfl | rfl
    · have hS : S = 2 ^ (2 * W) * (1 + 2 * q) := by rw [pow_succ] at hq; linear_combination hq
      refine ⟨⟨_, hS⟩, ?_⟩
      rw [hS, Int.mul_ediv_cancel_left _ h2W]
      exact ⟨q, by ring⟩
    · have hS : S = 2 ^ (2 * W) * (-1 + 2 * q) := by rw [pow_succ] at hq; linear_combination hq
      refine ⟨⟨_, hS⟩, ?_⟩
      rw [hS, Int.mul_ediv_cancel_left _ h2W]
      exact ⟨q - 1, by ring⟩
  · rw [if_neg hb, sub_zero] at hq
    refine ⟨fun ho => ?_, fun h => absurd h hb⟩
    have hS : S = 2 ^ (2 * W) * (2 * q) := by rw [hq, pow_succ]; ring
    obtain ⟨-, hodd⟩ := ho
    rw [hS, Int.mul_ediv_cancel_left _ h2W] at hodd
    obtain ⟨m, hm⟩ := hodd
    omega

/-! ### the algorithm recovers the unique minimum perfect matching -/

theorem term_p_form {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (w : G.edgeSet → ℕ)
    {M0 : Finset G.edgeSet} (hM0 : IsPerfectMatchingEdges G M0) :
    term (weightedTutteMatrix G w) (pperm hM0) = 2 ^ (2 * setWeight w M0) ∨
      term (weightedTutteMatrix G w) (pperm hM0) = -2 ^ (2 * setWeight w M0) :=
  two_pow_form _ _ (by rw [term_natAbs G w _ (pperm_adj hM0), wt_p w hM0])

theorem fin_form (D T : ℤ) (W : ℕ) (hT : T = 2 ^ (2 * W) ∨ T = -2 ^ (2 * W))
    (h : (2:ℤ) ^ (2 * W + 1) ∣ D - T) :
    D ≠ 0 ∧ (2:ℤ) ^ (2 * W) ∣ D ∧ ¬ (2:ℤ) ^ (2 * W + 1) ∣ D := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨u, hu, hD⟩ : ∃ u : ℤ, (u = 1 + 2 * q ∨ u = -1 + 2 * q) ∧ D = 2 ^ (2 * W) * u := by
    rcases hT with rfl | rfl
    · exact ⟨1 + 2 * q, Or.inl rfl, by rw [pow_succ] at hq; linear_combination hq⟩
    · exact ⟨-1 + 2 * q, Or.inr rfl, by rw [pow_succ] at hq; linear_combination hq⟩
  have hu0 : u ≠ 0 := by rcases hu with rfl | rfl <;> omega
  have h2W : (2:ℤ) ^ (2 * W) ≠ 0 := pow_ne_zero _ two_ne_zero
  refine ⟨by rw [hD]; exact mul_ne_zero h2W hu0, ⟨u, hD⟩, ?_⟩
  rintro ⟨r, hr⟩
  rw [hD, pow_succ] at hr
  have hur : u = 2 * r := by
    apply mul_left_cancel₀ h2W
    rw [hr]; ring
  rcases hu with rfl | rfl <;> omega

theorem main {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (w : G.edgeSet → ℕ) (M : Finset G.edgeSet) (hM : IsPerfectMatchingEdges G M)
    (huniq : ∀ M' : Finset G.edgeSet, IsPerfectMatchingEdges G M' → M' ≠ M →
      setWeight w M < setWeight w M') :
    (weightedTutteMatrix G w).det ≠ 0 ∧
      (2 : ℤ) ^ (2 * setWeight w M) ∣ (weightedTutteMatrix G w).det ∧
      ¬ (2 : ℤ) ^ (2 * setWeight w M + 1) ∣ (weightedTutteMatrix G w).det := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hM0 : M = ∅ := by
      ext e
      obtain ⟨x, hx⟩ := e
      induction x using Sym2.ind with
      | h a b => exact a.elim0
    have hW : setWeight w M = 0 := by rw [hM0]; simp [setWeight]
    rw [hW, Matrix.det_isEmpty]
    norm_num
  · exact fin_form _ _ _ (term_p_form w hM)
      (det_cong w hM (fun M' h1 h2 => huniq M' h1 h2) ⟨0, hn⟩)

end Q53d

open MulmuleyVV.Matching in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : G.edgeSet → ℕ) (M : Finset G.edgeSet) (hM : IsPerfectMatchingEdges G M)
    (huniq : ∀ M' : Finset G.edgeSet, IsPerfectMatchingEdges G M' → M' ≠ M →
      setWeight w M < setWeight w M') :
    (weightedTutteMatrix G w).det ≠ 0 ∧
      (2 : ℤ) ^ (2 * setWeight w M) ∣ (weightedTutteMatrix G w).det ∧
      ¬ (2 : ℤ) ^ (2 * setWeight w M + 1) ∣ (weightedTutteMatrix G w).det := by
  exact Q53d.main w M hM huniq
