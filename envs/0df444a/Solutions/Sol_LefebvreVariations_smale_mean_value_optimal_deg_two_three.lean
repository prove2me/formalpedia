-- Prove2me | solution 1 for LefebvreVariations.smale_mean_value_optimal_deg_two_three
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:31:07.35106+00:00
-- url     : https://prove2.me/submissions/7bb8a050-7744-47ce-a0e6-879a872abc59

import Mathlib

set_option autoImplicit false

open Polynomial

/-- The two failure discs are disjoint: the sum of the two defects is `6‖2u - δ‖² ≥ 0`. -/
private lemma key (u δ : ℂ) : ‖2 * u - 3 * δ‖ ≤ 4 * ‖u - δ‖ ∨ ‖2 * u + δ‖ ≤ 4 * ‖u‖ := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have e1 := mul_self_lt_mul_self (by positivity) h1
  have e2 := mul_self_lt_mul_self (by positivity) h2
  have n : ∀ w : ℂ, ‖w‖ * ‖w‖ = w.re * w.re + w.im * w.im := fun w => by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, sq]
  have e1' : 16 * (‖u - δ‖ * ‖u - δ‖) < ‖2 * u - 3 * δ‖ * ‖2 * u - 3 * δ‖ := by nlinarith
  have e2' : 16 * (‖u‖ * ‖u‖) < ‖2 * u + δ‖ * ‖2 * u + δ‖ := by nlinarith
  rw [n, n] at e1' e2'
  simp at e1' e2'
  nlinarith [sq_nonneg (2 * u.re - δ.re), sq_nonneg (2 * u.im - δ.im)]

private lemma eval_eq (P : ℂ[X]) (hP3 : P.natDegree ≤ 3) (x : ℂ) :
    P.eval x = P.coeff 3 * x ^ 3 + P.coeff 2 * x ^ 2 + P.coeff 1 * x + P.coeff 0 := by
  rw [eval_eq_sum_range' (n := 4) (by omega)]
  simp [Finset.sum_range_succ]
  ring

private lemma deval_eq (P : ℂ[X]) (hP3 : P.natDegree ≤ 3) (x : ℂ) :
    P.derivative.eval x = 3 * P.coeff 3 * x ^ 2 + 2 * P.coeff 2 * x + P.coeff 1 := by
  have hd : P.derivative.natDegree < 4 :=
    lt_of_le_of_lt (natDegree_derivative_le P) (by omega)
  have h4 : P.coeff 4 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [eval_eq_sum_range' hd]
  simp [Finset.sum_range_succ, coeff_derivative, h4]
  ring

theorem solution (P : ℂ[X]) (hP2 : 2 ≤ P.natDegree)
    (hP3 : P.natDegree ≤ 3) (z : ℂ) (hz : P.derivative.eval z ≠ 0) :
    ∃ c : ℂ, P.derivative.eval c = 0 ∧
      ‖(P.eval z - P.eval c) / (z - c)‖ ≤
        (((P.natDegree : ℝ) - 1) / P.natDegree) * ‖P.derivative.eval z‖ := by
  have hE := eval_eq P hP3
  have hD := deval_eq P hP3
  have hlc : P.coeff P.natDegree ≠ 0 := by
    have : P ≠ 0 := by rintro rfl; simp at hP2
    exact leadingCoeff_ne_zero.mpr this
  have hzc : ∀ c : ℂ, P.derivative.eval c = 0 → z - c ≠ 0 := fun c hc h =>
    hz (by rw [sub_eq_zero.mp h]; exact hc)
  set a := P.coeff 3
  set b := P.coeff 2
  set e := P.coeff 1
  rcases (show P.natDegree = 2 ∨ P.natDegree = 3 by omega) with hd | hd
  · -- degree 2: the ratio is exactly one half
    have ha : a = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hd] at hlc
    have hb0 : b ≠ 0 := hlc
    have hc : P.derivative.eval (-e / (2 * b)) = 0 := by
      rw [hD, ha]; field_simp; ring
    refine ⟨-e / (2 * b), hc, ?_⟩
    have hz' := hzc _ hc
    have h1 : (P.eval z - P.eval (-e / (2 * b))) / (z - -e / (2 * b))
        = b * (z - -e / (2 * b)) := by
      rw [div_eq_iff hz', hE, hE, ha]; field_simp; ring
    have h2 : P.derivative.eval z = 2 * (b * (z - -e / (2 * b))) := by
      rw [hD, ha]; field_simp; ring
    rw [h1, h2, hd, norm_mul (2 : ℂ)]
    norm_num
    linarith
  · -- degree 3: two critical points, one of them works
    rw [hd] at hlc
    have ha0 : a ≠ 0 := hlc
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (4 * b ^ 2 - 12 * a * e) (n := 2) (by norm_num)
    set c₁ := (-2 * b + s) / (6 * a)
    set c₂ := (-2 * b - s) / (6 * a)
    have hb : 2 * b = -3 * a * (c₁ + c₂) := by
      simp only [c₁, c₂]; field_simp; ring
    have he : e = 3 * a * (c₁ * c₂) := by
      simp only [c₁, c₂]; field_simp; linear_combination (3 : ℂ) * hs
    have hfac : ∀ x, P.derivative.eval x = 3 * a * (x - c₁) * (x - c₂) := fun x => by
      rw [hD]; linear_combination x * hb + he
    have hdif : ∀ c, P.eval z - P.eval c = a * (z ^ 3 - c ^ 3) + b * (z ^ 2 - c ^ 2)
        + e * (z - c) := fun c => by rw [hE, hE]; ring
    have hr : ((((P.natDegree : ℝ) - 1) / P.natDegree)) = 2 / 3 := by rw [hd]; norm_num
    rw [hr]
    have hc₁ : P.derivative.eval c₁ = 0 := by rw [hfac]; ring
    have hc₂ : P.derivative.eval c₂ = 0 := by rw [hfac]; ring
    rcases key (z - c₁) (c₂ - c₁) with hk | hk
    · refine ⟨c₁, hc₁, ?_⟩
      have h1 : (P.eval z - P.eval c₁) / (z - c₁)
          = a * (z - c₁) * (2 * (z - c₁) - 3 * (c₂ - c₁)) / 2 := by
        rw [div_eq_iff (hzc _ hc₁), hdif]
        linear_combination ((z ^ 2 - c₁ ^ 2) / 2) * hb + (z - c₁) * he
      have h2 : P.derivative.eval z = 3 * a * (z - c₁) * (z - c₂) := by
        rw [hfac]
      rw [sub_sub_sub_cancel_right] at hk
      rw [h1, h2]
      simp only [norm_mul, norm_div]
      norm_num
      nlinarith [mul_le_mul_of_nonneg_left hk
        (mul_nonneg (norm_nonneg a) (norm_nonneg (z - c₁)))]
    · refine ⟨c₂, hc₂, ?_⟩
      have h1 : (P.eval z - P.eval c₂) / (z - c₂)
          = a * (z - c₂) * (2 * (z - c₁) + (c₂ - c₁)) / 2 := by
        rw [div_eq_iff (hzc _ hc₂), hdif]
        linear_combination ((z ^ 2 - c₂ ^ 2) / 2) * hb + (z - c₂) * he
      have h2 : P.derivative.eval z = 3 * a * (z - c₂) * (z - c₁) := by
        rw [hfac]; ring
      rw [h1, h2]
      simp only [norm_mul, norm_div]
      norm_num
      nlinarith [mul_le_mul_of_nonneg_left hk
        (mul_nonneg (norm_nonneg a) (norm_nonneg (z - c₂)))]
