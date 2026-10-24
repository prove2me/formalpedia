-- Prove2me | solution 1 for HiringLP.ProbeTopK.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:45:58.749982+00:00
-- url     : https://prove2.me/submissions/43cd609c-8c10-41b2-bfd0-685931047094

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model

set_option autoImplicit false
open Finset HiringLP.ProbeTopK

namespace PTK2

noncomputable def sc {n J : ℕ} (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ) (r : Fin n → ℝ) (e : ℝ) :
    (Fin n → Fin J → ℝ) × (Fin n → ℝ) :=
  (fun i j => x i j * (1 + e * r i), fun i => y i * (1 + e * r i))

theorem sc_feas {n J : ℕ} (I : Instance n J) (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (hf : LPFeasible I x y) (r : Fin n → ℝ) (e : ℝ)
    (h1 : ∀ i, 0 ≤ 1 + e * r i) (h2 : ∀ i, y i * (1 + e * r i) ≤ 1)
    (h3 : ∑ i, y i * (1 + e * r i) ≤ I.T)
    (h4 : ∑ i, (∑ j, x i j) * (1 + e * r i) ≤ I.k) :
    LPFeasible I (sc x y r e).1 (sc x y r e).2 := by
  obtain ⟨hxq, -, -, hx0, hy⟩ := hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [sc]
    have := mul_le_mul_of_nonneg_right (hxq i j) (h1 i)
    linarith
  · exact h3
  · simp only [sc]
    have e1 : ∀ i, ∑ j, x i j * (1 + e * r i) = (∑ j, x i j) * (1 + e * r i) :=
      fun i => (sum_mul _ _ _).symm
    simp only [e1]; exact h4
  · intro i j; exact mul_nonneg (hx0 i j) (h1 i)
  · intro i; exact ⟨mul_nonneg (hy i).1 (h1 i), h2 i⟩

theorem not_ext {n J : ℕ} (I : Instance n J) (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (r : Fin n → ℝ) (e : ℝ) (he : e ≠ 0) (i0 : Fin n) (hi0 : y i0 * r i0 ≠ 0)
    (hp : LPFeasible I (sc x y r e).1 (sc x y r e).2)
    (hm : LPFeasible I (sc x y r (-e)).1 (sc x y r (-e)).2) :
    (x, y) ∉ Set.extremePoints ℝ (feasibleSet I) := by
  intro hext
  rw [mem_extremePoints] at hext
  have hseg : (x, y) ∈ openSegment ℝ (sc x y r e) (sc x y r (-e)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i j
    · simp only [sc, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [sc, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have := (hext.2 _ hp _ hm hseg).1
  have h := congrFun (congrArg Prod.snd this) i0
  simp only [sc] at h
  apply hi0
  have : e * (y i0 * r i0) = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' he
  · exact h'

theorem frac_bounds {n : ℕ} (y : Fin n → ℝ) (i : Fin n) (hi : i ∈ fracSet y) :
    0 < y i ∧ y i < 1 := by
  simpa [fracSet] using hi

theorem not_frac {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (i : Fin n)
    (hi : i ∉ fracSet y) : y i = 0 ∨ y i = 1 := by
  simp only [fracSet, mem_filter, mem_univ, true_and, not_and_or, not_lt] at hi
  rcases hi with h | h
  · left; linarith [(hy i).1]
  · right; linarith [(hy i).2]

/-- The perturbation argument: a nonzero direction supported on the fractional coordinates that
keeps the binding constraints fixed contradicts extremality. -/
theorem perturb {n J : ℕ} (I : Instance n J) (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (hext : (x, y) ∈ Set.extremePoints ℝ (feasibleSet I)) (r : Fin n → ℝ)
    (hsupp : ∀ i, r i ≠ 0 → i ∈ fracSet y)
    (hX : ∑ i, (∑ j, x i j) * r i = 0)
    (hY : ∑ i, y i * r i = 0 ∨ ∑ i, y i < I.T)
    (i0 : Fin n) (hi0 : r i0 ≠ 0) : False := by
  have hf : LPFeasible I x y := hext.1
  have hy := hf.2.2.2.2
  have hfr : (fracSet y).Nonempty := ⟨i0, hsupp i0 hi0⟩
  obtain ⟨i1, hi1, hmin⟩ := exists_min_image (fracSet y) (fun i => 1 - y i) hfr
  set m := 1 - y i1 with hm_def
  have hm0 : 0 < m := by have := (frac_bounds y i1 hi1).2; linarith
  set s : ℝ := if ∑ i, y i * r i = 0 then 1 else I.T - ∑ i, y i with hs_def
  have hs0 : 0 < s := by
    simp only [hs_def]
    split_ifs with h
    · norm_num
    · rcases hY with h' | h'
      · exact absurd h' h
      · linarith
  set R := ∑ i, |r i| + 1 with hR
  have hR0 : 0 < R := by
    have : 0 ≤ ∑ i, |r i| := sum_nonneg (fun i _ => abs_nonneg _)
    linarith
  set e := min m s / R with he_def
  have he0 : 0 < e := div_pos (lt_min hm0 hs0) hR0
  have hri : ∀ i, |r i| < R := by
    intro i
    have : |r i| ≤ ∑ i, |r i| := single_le_sum (f := fun i => |r i|) (fun i _ => abs_nonneg _)
      (mem_univ i)
    linarith
  have heri : ∀ i, |e * r i| ≤ min m s := by
    intro i
    rw [abs_mul, abs_of_pos he0, he_def, div_mul_eq_mul_div, div_le_iff₀ hR0]
    exact mul_le_mul_of_nonneg_left (hri i).le (le_min hm0.le hs0.le)
  have hsum_abs : |∑ i, y i * r i| ≤ ∑ i, |r i| := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i _ => ?_))
    rw [abs_mul, abs_of_nonneg (hy i).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hy i).2
  have feas : ∀ e' : ℝ, |e'| = e → LPFeasible I (sc x y r e').1 (sc x y r e').2 := by
    intro e' he'
    have heri' : ∀ i, |e' * r i| ≤ min m s := by
      intro i; rw [abs_mul, he', ← abs_of_pos he0, ← abs_mul]; exact heri i
    apply sc_feas I x y hf r e'
    · intro i
      have := heri' i
      have := neg_abs_le (e' * r i)
      have : min m s ≤ 1 := (min_le_left _ _).trans (by have := (hy i1).1; linarith)
      linarith
    · intro i
      by_cases hri0 : r i = 0
      · rw [hri0]; simp [(hy i).2]
      · have hfi := frac_bounds y i (hsupp i hri0)
        have h1 := hmin i (hsupp i hri0)
        have h2 := heri' i
        have h3 := le_abs_self (e' * r i)
        have : e' * r i ≤ 1 - y i := by
          have := min_le_left m s; linarith
        have : y i * (e' * r i) ≤ e' * r i ∨ e' * r i < 0 := by
          by_cases hneg : e' * r i < 0
          · right; exact hneg
          · left; exact mul_le_of_le_one_left (not_lt.1 hneg) hfi.2.le
        rcases this with h | h
        · nlinarith
        · nlinarith [hfi.1]
    · have e1 : ∑ i, y i * (1 + e' * r i) = ∑ i, y i + e' * ∑ i, y i * r i := by
        rw [mul_sum, ← sum_add_distrib]; apply sum_congr rfl; intro i _; ring
      rw [e1]
      by_cases h0 : ∑ i, y i * r i = 0
      · rw [h0, mul_zero, add_zero]; exact hf.2.1
      · have hsv : s = I.T - ∑ i, y i := by simp only [hs_def, if_neg h0]
        have : |e' * ∑ i, y i * r i| ≤ s := by
          rw [abs_mul, he']
          calc e * |∑ i, y i * r i| ≤ e * R :=
                mul_le_mul_of_nonneg_left (by linarith) he0.le
            _ = min m s := by rw [he_def]; field_simp
            _ ≤ s := min_le_right _ _
        have := le_abs_self (e' * ∑ i, y i * r i)
        linarith
    · have e1 : ∑ i, (∑ j, x i j) * (1 + e' * r i) =
          ∑ i, ∑ j, x i j + e' * ∑ i, (∑ j, x i j) * r i := by
        rw [mul_sum, ← sum_add_distrib]; apply sum_congr rfl; intro i _; ring
      rw [e1, hX, mul_zero, add_zero]; exact hf.2.2.1
  have hyi0 : y i0 ≠ 0 := (frac_bounds y i0 (hsupp i0 hi0)).1.ne'
  exact not_ext I x y r e he0.ne' i0 (mul_ne_zero hyi0 hi0)
    (feas e (abs_of_pos he0)) (feas (-e) (by rw [abs_neg, abs_of_pos he0])) hext

noncomputable def dlt {n : ℕ} (a : Fin n) (i : Fin n) : ℝ := if i = a then 1 else 0

theorem sum_dlt {n : ℕ} (f : Fin n → ℝ) (a : Fin n) : ∑ i, f i * dlt a i = f a := by
  simp [dlt]

end PTK2

open PTK2 in
theorem solution {n J : ℕ} (I : Instance n J) (hI : I.Valid)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (hext : (x, y) ∈ Set.extremePoints ℝ (feasibleSet I)) :
    (fracSet y).card ≤ 2 ∧ ((fracSet y).card = 2 → ∑ i ∈ fracSet y, y i = 1) := by
  have hf : LPFeasible I x y := hext.1
  have hy := hf.2.2.2.2
  set X : Fin n → ℝ := fun i => ∑ j, x i j with hXdef
  constructor
  · by_contra hcard
    push Not at hcard
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := two_lt_card_iff.1 hcard
    set D := y a * X b - y b * X a with hD
    by_cases hD0 : D = 0
    · let r : Fin n → ℝ := fun i => y b * dlt a i - y a * dlt b i
      have hsupp : ∀ i, r i ≠ 0 → i ∈ fracSet y := by
        intro i hi
        by_contra hni
        apply hi
        have h1 : i ≠ a := fun h => hni (h ▸ ha)
        have h2 : i ≠ b := fun h => hni (h ▸ hb)
        simp [r, dlt, h1, h2]
      have hlin : ∀ f : Fin n → ℝ, ∑ i, f i * r i = y b * f a - y a * f b := by
        intro f
        have : ∀ i, f i * r i = y b * (f i * dlt a i) - y a * (f i * dlt b i) := by
          intro i; simp only [r]; ring
        simp only [this, sum_sub_distrib, ← mul_sum, sum_dlt]
      apply perturb I x y hext r hsupp
      · rw [hlin]; simp only [hD] at hD0; linarith
      · left; rw [hlin]; ring
      · show r a ≠ 0
        simp only [r, dlt, ↓reduceIte, if_neg hab, mul_one, mul_zero, sub_zero]
        exact (frac_bounds y b hb).1.ne'
    · let r : Fin n → ℝ := fun i => (y b * X c - y c * X b) * dlt a i +
          (y c * X a - y a * X c) * dlt b i + D * dlt c i
      have hsupp : ∀ i, r i ≠ 0 → i ∈ fracSet y := by
        intro i hi
        by_contra hni
        apply hi
        have h1 : i ≠ a := fun h => hni (h ▸ ha)
        have h2 : i ≠ b := fun h => hni (h ▸ hb)
        have h3 : i ≠ c := fun h => hni (h ▸ hc)
        simp [r, dlt, h1, h2, h3]
      have hlin : ∀ f : Fin n → ℝ, ∑ i, f i * r i = (y b * X c - y c * X b) * f a +
          (y c * X a - y a * X c) * f b + D * f c := by
        intro f
        have : ∀ i, f i * r i = (y b * X c - y c * X b) * (f i * dlt a i) +
            (y c * X a - y a * X c) * (f i * dlt b i) + D * (f i * dlt c i) := by
          intro i; simp only [r]; ring
        simp only [this, sum_add_distrib, ← mul_sum, sum_dlt]
      apply perturb I x y hext r hsupp
      · rw [hlin]; simp only [hD]; ring
      · left; rw [hlin]; simp only [hD]; ring
      · show r c ≠ 0
        simp only [r, dlt, ↓reduceIte, if_neg (Ne.symm hac), if_neg (Ne.symm hbc), mul_one,
          mul_zero, zero_add]
        exact hD0
  · intro h2
    by_contra hs1
    obtain ⟨a, b, hab, hfr⟩ := card_eq_two.1 h2
    have ha : a ∈ fracSet y := by rw [hfr]; simp
    have hb : b ∈ fracSet y := by rw [hfr]; simp
    have hsab : ∑ i ∈ fracSet y, y i = y a + y b := by rw [hfr, sum_pair hab]
    rw [hsab] at hs1
    -- the interview constraint is slack
    have hslack : ∑ i, y i < I.T := by
      have hdecomp : ∀ i, y i = (if i ∈ onesSet y then 1 else 0) +
          (if i ∈ fracSet y then y i else 0) := by
        intro i
        by_cases hif : i ∈ fracSet y
        · have := frac_bounds y i hif
          have hno : i ∉ onesSet y := by simp [onesSet]; linarith
          simp [hif, hno]
        · rcases not_frac y hy i hif with h | h
          · have hno : i ∉ onesSet y := by simp [onesSet, h]
            simp [hif, hno, h]
          · have hyes : i ∈ onesSet y := by simp [onesSet, h]
            simp [hif, hyes, h]
      have hsum : ∑ i, y i = ((onesSet y).card : ℝ) + (y a + y b) := by
        rw [sum_congr rfl (fun i _ => hdecomp i), sum_add_distrib, sum_boole, ← sum_filter]
        have e : (univ.filter fun i => i ∈ onesSet y) = onesSet y := by ext; simp
        have e2 : (univ.filter fun i => i ∈ fracSet y) = fracSet y := by ext; simp
        rw [e, e2, ← hsab]
      rcases lt_or_eq_of_le hf.2.1 with h | h
      · exact h
      · exfalso
        rw [hsum] at h
        have hpa := frac_bounds y a ha
        have hpb := frac_bounds y b hb
        have hint : ((I.T : ℤ) - (onesSet y).card : ℤ) = 1 := by
          have h1 : (0 : ℝ) < ((I.T : ℤ) - (onesSet y).card : ℤ) := by push_cast; linarith
          have h2 : (((I.T : ℤ) - (onesSet y).card : ℤ) : ℝ) < 2 := by push_cast; linarith
          have h1' : (0 : ℤ) < (I.T : ℤ) - (onesSet y).card := by exact_mod_cast h1
          have h2' : (I.T : ℤ) - (onesSet y).card < 2 := by exact_mod_cast h2
          omega
        have : ((((I.T : ℤ) - (onesSet y).card : ℤ)) : ℝ) = 1 := by exact_mod_cast hint
        push_cast at this
        apply hs1; linarith
    by_cases hX0 : X a = 0 ∧ X b = 0
    · apply perturb I x y hext (dlt a)
      · intro i hi
        by_contra hni
        apply hi
        have h1 : i ≠ a := fun h => hni (h ▸ ha)
        simp [dlt, h1]
      · rw [sum_dlt]; exact hX0.1
      · right; exact hslack
      · show dlt a a ≠ 0
        simp [dlt]
    · let r : Fin n → ℝ := fun i => X b * dlt a i - X a * dlt b i
      have hlin : ∀ f : Fin n → ℝ, ∑ i, f i * r i = X b * f a - X a * f b := by
        intro f
        have : ∀ i, f i * r i = X b * (f i * dlt a i) - X a * (f i * dlt b i) := by
          intro i; simp only [r]; ring
        simp only [this, sum_sub_distrib, ← mul_sum, sum_dlt]
      have hsupp : ∀ i, r i ≠ 0 → i ∈ fracSet y := by
        intro i hi
        by_contra hni
        apply hi
        have h1 : i ≠ a := fun h => hni (h ▸ ha)
        have h2 : i ≠ b := fun h => hni (h ▸ hb)
        simp [r, dlt, h1, h2]
      by_cases hXb : X b = 0
      · have hXa : X a ≠ 0 := fun h => hX0 ⟨h, hXb⟩
        apply perturb I x y hext r hsupp
        · rw [hlin]; ring
        · right; exact hslack
        · show r b ≠ 0
          simp only [r, dlt, ↓reduceIte, if_neg (Ne.symm hab), mul_one, mul_zero, zero_sub]
          exact neg_ne_zero.2 hXa
      · apply perturb I x y hext r hsupp
        · rw [hlin]; ring
        · right; exact hslack
        · show r a ≠ 0
          simp only [r, dlt, ↓reduceIte, if_neg hab, mul_one, mul_zero, sub_zero]
          exact hXb
