-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.product_coeff_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T19:09:58.824114+00:00
-- url     : https://prove2.me/submissions/2d14f363-200c-4238-8622-a0900a6e6df1

import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

open scoped BigOperators

theorem solution
    {σ ι R : Type*} [DecidableEq σ] [CommSemiring R]
    (s : Finset ι) (f : ι → MvPowerSeries σ R) (n : σ →₀ ℕ)
    (hs : ∀ i ∈ s, ∀ m : σ →₀ ℕ,
      MvPowerSeries.coeff m (f i) ≠ 0 → m.sum (fun _ k => k) ≤ 1)
    (h : s.card < n.sum (fun _ k => k)) :
    MvPowerSeries.coeff n (∏ i ∈ s, f i) = 0 := by
  classical
  change s.card < n.degree at h
  rw [MvPowerSeries.coeff_prod]
  apply Finset.sum_eq_zero
  intro l hl
  by_contra hterm
  have hb : ∀ i ∈ s, (l i).degree ≤ 1 := by
    intro i hi
    exact hs i hi (l i) (fun hc => hterm (Finset.prod_eq_zero hi hc))
  have htotal : n.degree ≤ s.card := by
    calc
      n.degree = (∑ i ∈ s, l i).degree :=
        congrArg (fun m : σ →₀ ℕ => m.degree)
          (Finset.mem_finsuppAntidiag.mp hl).1.symm
      _ = ∑ i ∈ s, (l i).degree :=
        map_sum (Finsupp.degree : (σ →₀ ℕ) →+ ℕ) (fun i => l i) s
      _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum hb
      _ = s.card := by simp
  exact (Nat.not_le_of_lt h) htotal
