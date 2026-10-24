-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.coeff_prod_eq_of_first_jet_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:18:04.965757+00:00
-- url     : https://prove2.me/submissions/6414081d-8c10-4e5a-b8b0-156175acf80b

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

namespace E103FJ

theorem prod_order {ι : Type} {K : Type} [CommSemiring K] {σ : Type}
    (A : σ → MvPowerSeries ι K) (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0)
    (s : Finset σ) : (s.card : ℕ∞) ≤ (∏ j ∈ s, A j).order := by
  refine le_trans ?_ (MvPowerSeries.le_order_prod _ _)
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simpa using MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (hA i)

theorem key {ι : Type} [DecidableEq ι] {K : Type} [CommSemiring K] {σ : Type} [DecidableEq σ]
    (A B : σ → MvPowerSeries ι K)
    (hA0 : ∀ j, MvPowerSeries.constantCoeff (A j) = 0)
    (hB0 : ∀ j, MvPowerSeries.constantCoeff (B j) = 0)
    (h1 : ∀ j (p : ι →₀ ℕ), p.degree = 1 → MvPowerSeries.coeff p (A j) = MvPowerSeries.coeff p (B j))
    (s : Finset σ) : ∀ e : ι →₀ ℕ, e.degree ≤ s.card →
      MvPowerSeries.coeff e (∏ j ∈ s, A j) = MvPowerSeries.coeff e (∏ j ∈ s, B j) := by
  induction s using Finset.induction_on with
  | empty => intro e _; simp
  | insert j s hj ih =>
    intro e he
    rw [Finset.prod_insert hj, Finset.prod_insert hj, MvPowerSeries.coeff_mul,
      MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun pq hpq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    have hdeg : pq.1.degree + pq.2.degree = e.degree := by rw [← map_add, hpq]
    rw [Finset.card_insert_of_notMem hj] at he
    rcases Nat.lt_or_ge pq.1.degree 2 with hp | hp
    · interval_cases h : pq.1.degree
      · have : pq.1 = 0 := (Finsupp.degree_eq_zero_iff _).mp h
        rw [this, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
          MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hA0, hB0]
        simp
      · rw [h1 j _ h, ih _ (by omega)]
    · have hq : (pq.2.degree : ℕ∞) < s.card := by exact_mod_cast (by omega : pq.2.degree < s.card)
      rw [MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le hq (prod_order A hA0 s)),
        MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le hq (prod_order B hB0 s)), mul_zero, mul_zero]

end E103FJ

theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [CommSemiring K]
    {σ : Type} [Fintype σ]
    (A B : σ → MvPowerSeries ι K)
    (hAB : ∀ (j : σ) (d : ι → Nat),
      (∑ k : ι, d k) ≤ 1 →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (A j) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (B j))
    (hBzero : ∀ j : σ,
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun _ : ι => 0)) (B j) = 0)
    (e : ι → Nat)
    (he : (∑ k : ι, e k) = Fintype.card σ) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (∏ j : σ, A j) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (∏ j : σ, B j) := by
  classical
  have hz : Finsupp.equivFunOnFinite.symm (fun _ : ι => 0) = (0 : ι →₀ ℕ) := by
    ext; simp
  have hB0 : ∀ j, MvPowerSeries.constantCoeff (B j) = 0 := by
    intro j; have := hBzero j; rw [hz] at this; simpa using this
  have hA0 : ∀ j, MvPowerSeries.constantCoeff (A j) = 0 := by
    intro j
    have := hAB j (fun _ => 0) (by simp)
    rw [hz] at this
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, this,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hB0]
  have h1 : ∀ j (p : ι →₀ ℕ), p.degree = 1 →
      MvPowerSeries.coeff p (A j) = MvPowerSeries.coeff p (B j) := by
    intro j p hp
    have := hAB j p (by rw [Finsupp.degree_eq_sum] at hp; omega)
    simpa using this
  apply E103FJ.key A B hA0 hB0 h1 Finset.univ
  rw [Finsupp.degree_eq_sum, Finset.card_univ]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  omega
