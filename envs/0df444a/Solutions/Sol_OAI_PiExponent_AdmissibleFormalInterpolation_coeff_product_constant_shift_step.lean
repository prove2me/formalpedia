-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T10:59:14.78495+00:00
-- url     : https://prove2.me/submissions/8d852d3c-cc2f-4f0d-a681-a89f623cc0c1

import Mathlib.RingTheory.MvPowerSeries.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (k : ℕ) (φ : MvPowerSeries σ R) (c : R)
    (hbound : ∀ n : σ →₀ ℕ, k < n.sum (fun _ m => m) → MvPowerSeries.coeff n φ = 0)
    (htop : MvPowerSeries.coeff (Finsupp.single x k) φ = 1) :
    MvPowerSeries.coeff (Finsupp.single x (k + 1))
      (φ * (MvPowerSeries.X x + MvPowerSeries.C c)) = 1 := by
  have hX : MvPowerSeries.coeff (Finsupp.single x (k + 1))
      (φ * MvPowerSeries.X x) = 1 := by
    rw [MvPowerSeries.X_def, Finsupp.single_add]
    simpa [htop] using
      (MvPowerSeries.coeff_add_mul_monomial (φ := φ)
        (m := Finsupp.single x k) (n := Finsupp.single x 1) (a := (1 : R)))
  have hdeg : (Finsupp.single x (k + 1)).sum (fun _ m => m) = k + 1 := by
    simp only [Finsupp.sum_single_index]
  have hzero : MvPowerSeries.coeff (Finsupp.single x (k + 1)) φ = 0 := by
    apply hbound
    rw [hdeg]
    exact Nat.lt_succ_self k
  calc
    MvPowerSeries.coeff (Finsupp.single x (k + 1))
        (φ * (MvPowerSeries.X x + MvPowerSeries.C c)) =
      MvPowerSeries.coeff (Finsupp.single x (k + 1)) (φ * MvPowerSeries.X x) +
        MvPowerSeries.coeff (Finsupp.single x (k + 1)) (φ * MvPowerSeries.C c) := by
          rw [mul_add, map_add]
    _ = 1 + 0 := by rw [hX, MvPowerSeries.coeff_mul_C, hzero]; simp
    _ = 1 := by simp