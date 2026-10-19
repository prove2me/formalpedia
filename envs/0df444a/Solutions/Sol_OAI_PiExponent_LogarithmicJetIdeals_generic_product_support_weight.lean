-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.generic_product_support_weight
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T02:53:42.743945+00:00
-- url     : https://prove2.me/submissions/8c38776f-8a8b-47eb-9e24-ec44461932af

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.MvPowerSeries.Basic

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

private theorem weighted_support_mul
    {n : ℕ} (q : Fin n → ℝ)
    (f g : MvPowerSeries (Fin n) ℂ) (a b : ℝ)
    (hf : ∀ c : Fin n →₀ ℕ, MvPowerSeries.coeff c f ≠ 0 →
      a ≤ ∑ j, q j * (c j : ℝ))
    (hg : ∀ c : Fin n →₀ ℕ, MvPowerSeries.coeff c g ≠ 0 →
      b ≤ ∑ j, q j * (c j : ℝ))
    (e : Fin n →₀ ℕ)
    (he : MvPowerSeries.coeff e (f * g) ≠ 0) :
    a + b ≤ ∑ j, q j * (e j : ℝ) := by
  classical
  rw [MvPowerSeries.coeff_mul] at he
  obtain ⟨⟨c, d⟩, hcd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have hc : MvPowerSeries.coeff c f ≠ 0 := by
    intro hc
    apply hne
    rw [hc, zero_mul]
  have hd : MvPowerSeries.coeff d g ≠ 0 := by
    intro hd
    apply hne
    rw [hd, mul_zero]
  have hadd : c + d = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hcd
  calc
    a + b ≤ (∑ j, q j * (c j : ℝ)) + (∑ j, q j * (d j : ℝ)) :=
      add_le_add (hf c hc) (hg d hd)
    _ = ∑ j, q j * ((c + d) j : ℝ) := by
      simp only [Finsupp.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
    _ = ∑ j, q j * (e j : ℝ) := by rw [hadd]

theorem solution
    {n : ℕ} (q : Fin n → ℝ)
    (sigma : Fin n → MvPowerSeries (Fin n) ℂ)
    (hsigma : ∀ i : Fin n, ∀ c : Fin n →₀ ℕ,
      MvPowerSeries.coeff c (sigma i) ≠ 0 →
        q i ≤ ∑ j, q j * (c j : ℝ))
    (b : Fin n → ℕ) (e : Fin n →₀ ℕ)
    (hprod : MvPowerSeries.coeff e (∏ i, sigma i ^ b i) ≠ 0) :
    (∑ j, q j * (b j : ℝ)) ≤ ∑ j, q j * (e j : ℝ) := by
  classical
  -- The unit series is supported only at the zero exponent.
  have hone : ∀ c : Fin n →₀ ℕ,
      MvPowerSeries.coeff c (1 : MvPowerSeries (Fin n) ℂ) ≠ 0 →
        (0 : ℝ) ≤ ∑ j, q j * (c j : ℝ) := by
    intro c hc
    have hc0 : c = 0 := by
      by_contra h
      apply hc
      simp only [MvPowerSeries.coeff_one, if_neg h]
    subst c
    simp
  -- Repeated multiplication adds one copy of the lower bound each time.
  have hpow : ∀ (i : Fin n) (k : ℕ) (c : Fin n →₀ ℕ),
      MvPowerSeries.coeff c (sigma i ^ k) ≠ 0 →
        q i * (k : ℝ) ≤ ∑ j, q j * (c j : ℝ) := by
    intro i k
    induction k with
    | zero =>
        simpa only [pow_zero, Nat.cast_zero, mul_zero] using hone
    | succ k ih =>
        intro c hc
        rw [pow_succ] at hc
        have h := weighted_support_mul q (sigma i ^ k) (sigma i)
          (q i * (k : ℝ)) (q i) ih (hsigma i) c hc
        simpa only [Nat.cast_succ, mul_add, mul_one] using h
  -- Sum the bounds while inserting the factors of the finite product.
  have hfinite : ∀ s : Finset (Fin n), ∀ c : Fin n →₀ ℕ,
      MvPowerSeries.coeff c (∏ i ∈ s, sigma i ^ b i) ≠ 0 →
        (∑ i ∈ s, q i * (b i : ℝ)) ≤ ∑ j, q j * (c j : ℝ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.prod_empty, Finset.sum_empty] using hone
    | @insert i s hi ih =>
        intro c hc
        rw [Finset.prod_insert hi] at hc
        have h := weighted_support_mul q (sigma i ^ b i)
          (∏ j ∈ s, sigma j ^ b j)
          (q i * (b i : ℝ)) (∑ j ∈ s, q j * (b j : ℝ))
          (hpow i (b i)) ih c hc
        simpa only [Finset.sum_insert hi] using h
  exact hfinite Finset.univ e hprod
