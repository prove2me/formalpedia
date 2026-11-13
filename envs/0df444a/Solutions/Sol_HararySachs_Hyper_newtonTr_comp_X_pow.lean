-- Prove2me | solution 1 for HararySachs.Hyper.newtonTr_comp_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T04:44:16.605022+00:00
-- url     : https://prove2.me/submissions/79d8df36-ce21-469e-84c1-a7e920616d90

import Mathlib
import Definitions.Def_HararySachs_Hyper_TensorPhi

open HararySachs.Hyper Finset

namespace NewtonCompAux

variable {R : Type*} [CommRing R]

/-- Newton's identities in the form `n Φ_n = -Σ_{a+b=n} τ_a Φ_b`, valid for all `n`. -/
lemma newton_anti (Φ : Polynomial R) (h0 : Φ.coeff 0 = 1) (n : ℕ) :
    (n : R) * Φ.coeff n = -∑ p ∈ antidiagonal n, newtonTr Φ p.1 * Φ.coeff p.2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => newtonTr Φ a * Φ.coeff b)]
  cases n with
  | zero => simp [newtonTr]
  | succ e =>
    rw [sum_range_succ, Nat.sub_self, h0, mul_one, newtonTr.eq_2,
      ← Fin.sum_univ_eq_sum_range (fun j => newtonTr Φ j * Φ.coeff (e + 1 - j))]
    ring

/-- Newton's recursion determines the traces uniquely. -/
lemma newtonTr_unique (Φ : Polynomial R) (h0 : Φ.coeff 0 = 1) (t : ℕ → R) (ht0 : t 0 = 0)
    (ht : ∀ n : ℕ, (n : R) * Φ.coeff n = -∑ p ∈ antidiagonal n, t p.1 * Φ.coeff p.2)
    (m : ℕ) : newtonTr Φ m = t m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => rw [newtonTr, ht0]
    | succ e =>
      have h := ht (e + 1)
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => t a * Φ.coeff b),
        sum_range_succ, Nat.sub_self, h0, mul_one] at h
      rw [newtonTr.eq_2,
        Fin.sum_univ_eq_sum_range (fun j => newtonTr Φ j * Φ.coeff (e + 1 - j))]
      have hs : ∑ j ∈ range (e + 1), newtonTr Φ j * Φ.coeff (e + 1 - j) =
          ∑ j ∈ range (e + 1), t j * Φ.coeff (e + 1 - j) :=
        sum_congr rfl fun j hj => by rw [ih j (mem_range.mp hj)]
      rw [hs]
      linear_combination -h

end NewtonCompAux

open NewtonCompAux in
theorem solution {R : Type*} [CommRing R] (Φ : Polynomial R) (h : Φ.coeff 0 = 1)
    (r : ℕ) (hr : 1 ≤ r) (d : ℕ) :
    newtonTr (Φ.comp (Polynomial.X ^ r)) (r * d) = (r : R) * newtonTr Φ d := by
  classical
  have hr0 : 0 < r := by omega
  -- coefficients of `Φ(ζ^r)`
  have hΨ : ∀ n, (Φ.comp (Polynomial.X ^ r)).coeff n =
      if r ∣ n then Φ.coeff (n / r) else 0 := fun n => by
    rw [← Polynomial.expand_eq_comp_X_pow, Polynomial.coeff_expand hr0]
  have h0 : (Φ.comp (Polynomial.X ^ r)).coeff 0 = 1 := by
    rw [hΨ, if_pos (dvd_zero r), Nat.zero_div, h]
  -- the candidate traces
  set t : ℕ → R := fun a => if r ∣ a then (r : R) * newtonTr Φ (a / r) else 0 with ht
  have key := newtonTr_unique (Φ.comp (Polynomial.X ^ r)) h0 t
    (by simp [ht, newtonTr]) (fun n => ?_) (r * d)
  · rw [key, ht]
    simp only
    rw [if_pos (dvd_mul_right r d), Nat.mul_div_cancel_left d hr0]
  -- Newton's identities for `Φ(ζ^r)` with the candidate traces
  by_cases hn : r ∣ n
  · obtain ⟨c, rfl⟩ := hn
    have hsum : ∑ p ∈ antidiagonal (r * c), t p.1 * (Φ.comp (Polynomial.X ^ r)).coeff p.2 =
        ∑ q ∈ antidiagonal c, (r : R) * newtonTr Φ q.1 * Φ.coeff q.2 := by
      set f : ℕ × ℕ → ℕ × ℕ := fun q => (r * q.1, r * q.2) with hf
      have hinj : Set.InjOn f (antidiagonal c) := by
        intro q₁ _ q₂ _ hq
        simp only [hf, Prod.mk.injEq] at hq
        exact Prod.ext (Nat.eq_of_mul_eq_mul_left hr0 hq.1) (Nat.eq_of_mul_eq_mul_left hr0 hq.2)
      have hsub : (antidiagonal c).image f ⊆ antidiagonal (r * c) := by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
        rw [HasAntidiagonal.mem_antidiagonal] at hq ⊢
        simp only [hf, ← mul_add, hq]
      rw [← sum_subset hsub, sum_image hinj]
      · refine sum_congr rfl fun q _ => ?_
        simp only [hf, ht, hΨ, if_pos (dvd_mul_right r _), Nat.mul_div_cancel_left _ hr0]
      · intro p hp hnot
        rw [HasAntidiagonal.mem_antidiagonal] at hp
        by_cases ha : r ∣ p.1
        · by_cases hb : r ∣ p.2
          · exfalso
            obtain ⟨a', ha'⟩ := ha
            obtain ⟨b', hb'⟩ := hb
            apply hnot
            refine mem_image.mpr ⟨(a', b'), ?_, ?_⟩
            · rw [HasAntidiagonal.mem_antidiagonal]
              apply Nat.eq_of_mul_eq_mul_left hr0
              rw [mul_add, ← ha', ← hb', hp]
            · simp only [hf, ← ha', ← hb']
          · rw [hΨ, if_neg hb, mul_zero]
        · simp only [ht, if_neg ha, zero_mul]
    rw [hsum, hΨ, if_pos (dvd_mul_right r c), Nat.mul_div_cancel_left c hr0]
    have hN := newton_anti Φ h c
    simp_rw [mul_assoc]
    rw [← mul_sum]
    push_cast
    linear_combination (r : R) * hN
  · rw [hΨ, if_neg hn, mul_zero]
    symm
    rw [neg_eq_zero]
    refine sum_eq_zero fun p hp => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    by_cases ha : r ∣ p.1
    · have hb : ¬ r ∣ p.2 := fun hb => hn (hp ▸ dvd_add ha hb)
      rw [hΨ, if_neg hb, mul_zero]
    · simp only [ht, if_neg ha, zero_mul]
