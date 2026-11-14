-- Prove2me | solution 1 for KSATSingleFlip.Connect.local_limit_empirical_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:06:11.240401+00:00
-- url     : https://prove2.me/submissions/d3d7a87c-d79e-4f53-bf72-389a87e75e8a

import Mathlib
set_option autoImplicit false
open scoped BigOperators

private theorem square_sum_bound {Ω : Type} [Fintype Ω] (n : ℕ) (hn : 1 ≤ n)
    (p : Ω → ℝ) (X : Fin n → Ω → ℝ) (C ε : ℝ)
    (hdiag : ∀ i : Fin n, (∑ ω, p ω * (X i ω)^2) ≤ C)
    (hoff : ∀ i j : Fin n, i ≠ j → (∑ ω, p ω * X i ω * X j ω) ≤ ε) :
    (∑ ω, p ω * (∑ i : Fin n, X i ω)^2) ≤
      (n:ℝ)*C + (n:ℝ)*((n:ℝ)-1)*ε := by
  classical
  have hid : (∑ ω, p ω * (∑ i : Fin n, X i ω)^2) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ ω, p ω * X i ω * X j ω := by
    calc
      _ = ∑ ω, ∑ i : Fin n, ∑ j : Fin n, p ω * X i ω * X j ω := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [pow_two, Finset.sum_mul_sum]
        simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ i : Fin n, ∑ ω, ∑ j : Fin n, p ω * X i ω * X j ω := Finset.sum_comm
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ ω, p ω * X i ω * X j ω := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
  rw [hid]
  have hrow (i : Fin n) : (∑ j : Fin n, ∑ ω, p ω * X i ω * X j ω) ≤ C + ((n:ℝ)-1)*ε := by
    calc
      _ ≤ ∑ j : Fin n, if i = j then C else ε := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i=j
        · subst j
          simpa [pow_two, mul_assoc] using hdiag i
        · simpa [hij] using hoff i j hij
      _ = C + ((n:ℝ)-1)*ε := by
        have hfunc : (fun j : Fin n => if i=j then C else ε) =
            (fun j => ε + if i=j then C-ε else 0) := by
          funext j
          by_cases h : i=j <;> simp [h]
        rw [hfunc, Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq]
        ring

  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ ω, p ω * X i ω * X j ω) ≤ ∑ _i : Fin n, (C + ((n:ℝ)-1)*ε) := Finset.sum_le_sum (fun i _ => hrow i)
    _ = (n:ℝ)*C + (n:ℝ)*((n:ℝ)-1)*ε := by simp; ring


theorem solution {Ω : Type} [Fintype Ω] (n : ℕ) (hn : 1 ≤ n)
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Fin n → Ω → ℝ)
    (C ε t : ℝ) (hε : 0 ≤ ε) (ht : 0 < t)
    (hdiag : ∀ i : Fin n, (∑ ω, p ω * (X i ω)^2) ≤ C)
    (hoff : ∀ i j : Fin n, i ≠ j → (∑ ω, p ω * X i ω * X j ω) ≤ ε) :
    (∑ ω, if t ≤ |(∑ i : Fin n, X i ω)/(n:ℝ)| then p ω else 0) ≤
      (C/(n:ℝ)+ε)/t^2 := by
  classical
  have hnr : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsq : 0 < (n:ℝ)^2 := sq_pos_of_pos hnr
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have hsum := square_sum_bound n hn p X C ε hdiag hoff
  have havg : (∑ ω, p ω * ((∑ i : Fin n, X i ω)/(n:ℝ))^2) ≤ C/(n:ℝ)+ε := by
    have hh := div_le_div_of_nonneg_right hsum (le_of_lt hsq)
    have hl : (∑ ω, p ω * ((∑ i : Fin n, X i ω)/(n:ℝ))^2) =
        (∑ ω, p ω * (∑ i : Fin n, X i ω)^2)/(n:ℝ)^2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [div_pow]
      ring
    rw [hl]
    apply hh.trans
    have hm : (0:ℝ) ≤ (n:ℝ)*ε := mul_nonneg (le_of_lt hnr) hε
    apply (div_le_iff₀ hsq).2
    field_simp
    nlinarith
  calc
    (∑ ω, if t ≤ |(∑ i : Fin n, X i ω)/(n:ℝ)| then p ω else 0) ≤
        ∑ ω, (p ω * ((∑ i : Fin n, X i ω)/(n:ℝ))^2)/t^2 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hh : t ≤ |(∑ i : Fin n, X i ω)/(n:ℝ)|
      · simp only [hh, if_true]
        apply (le_div_iff₀ ht2).2
        have hs : t^2 ≤ ((∑ i : Fin n, X i ω)/(n:ℝ))^2 := by
          nlinarith [sq_abs ((∑ i : Fin n, X i ω)/(n:ℝ)), abs_nonneg ((∑ i : Fin n, X i ω)/(n:ℝ))]
        exact mul_le_mul_of_nonneg_left hs (hp ω)
      · simp only [hh, if_false]
        exact div_nonneg (mul_nonneg (hp ω) (sq_nonneg _)) (le_of_lt ht2)
    _ = (∑ ω, p ω * ((∑ i : Fin n, X i ω)/(n:ℝ))^2)/t^2 := by rw [Finset.sum_div]
    _ ≤ (C/(n:ℝ)+ε)/t^2 := div_le_div_of_nonneg_right havg (le_of_lt ht2)
