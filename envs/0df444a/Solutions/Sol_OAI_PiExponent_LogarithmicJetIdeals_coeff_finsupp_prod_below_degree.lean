-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_finsupp_prod_below_degree
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:16:29.606575+00:00
-- url     : https://prove2.me/submissions/5613a1e7-c3ec-432f-b199-d7b549532678

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.Data.Finsupp.Weight

/-!
# Coefficients of a powered product below the total number of factors

Let `R i` be a family of multivariate power series over a commutative semiring `K`
which has the same coefficients as the variable `X i` in total degree `0` and `1`.
For an exponent vector `a : ι →₀ ℕ`, the `a`-weighted product
`a.prod (fun i k => R i ^ k)` is a product of exactly `∑ i, a i` series factors,
each of which has vanishing constant term.  Consequently every coefficient of
this product in total degree `< ∑ i, a i` vanishes.

On the other hand, the monomial `monomial a 1` has a coefficient at a different
exponent of the same total degree at most `∑ a` only if that exponent equals `a`;
since the exponent in question has total degree `< ∑ a`, its coefficient vanishes.

This is the statement proved below: for `e` with `∑ e < ∑ a`,
`[X^e] ∏_i R i^{a_i} = [X^e] monomial a 1 = 0`.

The formalization avoids subtraction (the coefficient ring is only a commutative
semiring) and works with the convolution formula for power-series coefficients.
-/

open scoped BigOperators

noncomputable section
open scoped BigOperators

namespace ProdBelow

/-- A finite product of series with prescribed vanishing lower bounds has no
coefficients in total degree below the sum of the bounds. -/
lemma coeff_finset_prod_eq_zero_of_lt_sum
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    {σ : Type} [Fintype σ] :
    ∀ (s : Finset σ) (f : σ → MvPowerSeries ι K) (m : σ → ℕ),
      (∀ j ∈ s, ∀ d : ι →₀ ℕ, Finsupp.degree d < m j →
        MvPowerSeries.coeff d (f j) = 0) →
      ∀ d : ι →₀ ℕ, Finsupp.degree d < ∑ j ∈ s, m j →
        MvPowerSeries.coeff d (∏ j ∈ s, f j) = 0 := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro f m hf d hd
      simp only [Finset.sum_empty] at hd
      exfalso
      omega
  | cons a s ha ih =>
      intro f m hf d hd
      rw [Finset.sum_cons ha] at hd
      rw [Finset.prod_cons ha, MvPowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨d1, d2⟩ := p
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have hdeg : Finsupp.degree d1 + Finsupp.degree d2 = Finsupp.degree d := by
        rw [← map_add, hp]
      by_cases h1 : Finsupp.degree d1 < m a
      · rw [hf a (Finset.mem_cons_self a s) d1 h1, zero_mul]
      · rw [ih f m (fun j hj => hf j (Finset.mem_cons_of_mem hj)) d2 (by omega), mul_zero]

/-- A power of a series with vanishing constant term has no coefficients in
total degree below its exponent. -/
lemma coeff_pow_eq_zero_of_lt
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    (f : MvPowerSeries ι K) (hf : MvPowerSeries.coeff 0 f = 0)
    (k : ℕ) (d : ι →₀ ℕ) (hd : Finsupp.degree d < k) :
    MvPowerSeries.coeff d (f ^ k) = 0 := by
  induction k generalizing d with
  | zero =>
      exfalso
      omega
  | succ k ih =>
      rw [pow_succ, MvPowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨d1, d2⟩ := p
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have hdeg : Finsupp.degree d1 + Finsupp.degree d2 = Finsupp.degree d := by
        rw [← map_add, hp]
      by_cases h2 : Finsupp.degree d2 = 0
      · have hd2 : d2 = 0 := (Finsupp.degree_eq_zero_iff d2).mp h2
        rw [hd2, hf, mul_zero]
      · rw [ih d1 (by omega), zero_mul]

end ProdBelow

open ProdBelow in
theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    (R : ι → MvPowerSeries ι K)
    (a : Finsupp ι Nat)
    (hR : ∀ (i : ι) (d : ι → Nat), (∑ k : ι, d k) ≤ 1 →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (R i) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (MvPowerSeries.X i))
    (e : ι → Nat)
    (he : (∑ k : ι, e k) < (∑ k : ι, a k)) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (a.prod fun i k => R i ^ k) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
        (MvPolynomial.monomial a (1 : K)) := by
  classical
  -- constant coefficients of the `R i` vanish
  have hR0 : ∀ i : ι, MvPowerSeries.coeff 0 (R i) = 0 := by
    intro i
    have h := hR i (fun _ => 0) (by simp)
    have h0 : Finsupp.equivFunOnFinite.symm (fun _ : ι => (0 : ℕ)) = 0 := by
      ext k
      simp
    rw [h0] at h
    simpa using h
  -- total degrees of `symm e` and of `a`
  have hdeg_e : Finsupp.degree (Finsupp.equivFunOnFinite.symm e) = ∑ k : ι, e k := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_congr rfl (fun k _ => congr_fun (Finsupp.coe_equivFunOnFinite_symm e) k)
  have hdeg_a : Finsupp.degree a = ∑ k : ι, a k := by
    rw [Finsupp.degree_eq_sum]
  have hsum : (∑ i ∈ a.support, a i) = ∑ k : ι, a k := by
    rw [← Finsupp.degree_apply, Finsupp.degree_eq_sum]
  -- the left-hand side vanishes
  have hlhs : MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (a.prod fun i k => R i ^ k) = 0 := by
    show MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (∏ i ∈ a.support, R i ^ a i) = 0
    apply coeff_finset_prod_eq_zero_of_lt_sum a.support (fun i => R i ^ a i) (fun i => a i)
    · intro i hi d hd
      exact coeff_pow_eq_zero_of_lt (R i) (hR0 i) (a i) d hd
    · rw [hdeg_e, hsum]
      exact he
  -- the right-hand side vanishes because the exponents differ
  have hrhs : MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.monomial a (1 : K)) = 0 := by
    rw [MvPolynomial.coeff_monomial]
    rw [if_neg]
    intro h
    have hdeg : (∑ k : ι, a k) = (∑ k : ι, e k) := by
      rw [← hdeg_a, h, hdeg_e]
    omega
  rw [hlhs, hrhs]
