-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.mvPowerSeries_aeval_monomial_coeff_eq_zero_of_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:18:00.749079+00:00
-- url     : https://prove2.me/submissions/ce07e2c9-6bd0-48b9-b587-ced9d6b12b26

import Mathlib
import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators
theorem pie_lw_mul {σ : Type*} {φ : (σ →₀ ℕ) → ℝ} (hφ : ∀ x y, φ (x + y) = φ x + φ y)
    {B B' : ℝ} {f g : MvPowerSeries σ ℂ}
    (hf : ∀ b, MvPowerSeries.coeff b f ≠ 0 → B ≤ φ b)
    (hg : ∀ b, MvPowerSeries.coeff b g ≠ 0 → B' ≤ φ b) :
    ∀ b, MvPowerSeries.coeff b (f * g) ≠ 0 → B + B' ≤ φ b := by
  classical
  intro b hb
  rw [MvPowerSeries.coeff_mul] at hb
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, hφ]
  exact add_le_add (hf _ (left_ne_zero_of_mul hne)) (hg _ (right_ne_zero_of_mul hne))

theorem solution
    {n : ℕ} (w : Fin n → ℝ)
    (F : Fin n → MvPowerSeries (Fin n) ℂ)
    (hF : ∀ (i : Fin n) (α : Fin n →₀ ℕ),
      (∑ j, w j * (α j : ℝ)) < w i →
        MvPowerSeries.coeff α (F i) = 0)
    (a b : Fin n → ℕ)
    (hab : (∑ i, w i * (b i : ℝ)) <
      (∑ i, w i * (a i : ℝ))) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (MvPolynomial.aeval F
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0 := by
  classical
  let φ : (Fin n →₀ ℕ) → ℝ := fun α => ∑ j, w j * (α j : ℝ)
  have hφ : ∀ x y, φ (x + y) = φ x + φ y := by
    intro x y; simp only [φ, Finsupp.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  have hFi : ∀ i, ∀ α, MvPowerSeries.coeff α (F i) ≠ 0 → w i ≤ φ α := by
    intro i α hα
    by_contra h
    push Not at h
    exact hα (hF i α h)
  have hpow : ∀ i (k : ℕ), ∀ α, MvPowerSeries.coeff α (F i ^ k) ≠ 0 → (k : ℝ) * w i ≤ φ α := by
    intro i k
    induction k with
    | zero =>
      intro α hα
      rw [pow_zero, MvPowerSeries.coeff_one] at hα
      split_ifs at hα with h
      · subst h; simp [φ]
      · exact absurd rfl hα
    | succ k ih =>
      intro α hα
      rw [pow_succ] at hα
      have := pie_lw_mul hφ ih (hFi i) α hα
      push_cast; linarith
  have hprod : ∀ s : Finset (Fin n), ∀ α,
      MvPowerSeries.coeff α (∏ i ∈ s, F i ^ a i) ≠ 0 → (∑ i ∈ s, (a i : ℝ) * w i) ≤ φ α := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro α hα
      rw [Finset.prod_empty, MvPowerSeries.coeff_one] at hα
      split_ifs at hα with h
      · subst h; simp [φ]
      · exact absurd rfl hα
    | insert x s hx ih =>
      intro α hα
      rw [Finset.prod_insert hx] at hα
      rw [Finset.sum_insert hx]
      exact pie_lw_mul hφ (hpow x (a x)) ih α hα
  by_contra hne
  have hmono : MvPolynomial.aeval F (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1) =
      ∏ i, F i ^ a i := by
    rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    rfl
  rw [hmono] at hne
  have := hprod Finset.univ _ hne
  have e1 : φ (InterpolationMatrix.exponentVector b) = ∑ i, w i * (b i : ℝ) := by
    simp [φ, InterpolationMatrix.exponentVector]
  rw [e1] at this
  have e2 : ∑ i, (a i : ℝ) * w i = ∑ i, w i * (a i : ℝ) := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  linarith
