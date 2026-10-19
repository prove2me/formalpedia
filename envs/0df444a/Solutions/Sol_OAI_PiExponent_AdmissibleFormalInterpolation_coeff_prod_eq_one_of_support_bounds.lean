-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.coeff_prod_eq_one_of_support_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:03:28.657474+00:00
-- url     : https://prove2.me/submissions/d2d5e6a7-bc27-45a8-a61c-594dcbc69306

import Mathlib.RingTheory.MvPowerSeries.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

theorem solution
    {σ R ι : Type*} [DecidableEq σ] [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (f : ι → MvPowerSeries σ R) (d : ι → (σ →₀ ℕ))
    (hsupport : ∀ i ∈ s, ∀ k : σ →₀ ℕ,
      MvPowerSeries.coeff k (f i) ≠ 0 → k ≤ d i)
    (htop : ∀ i ∈ s, MvPowerSeries.coeff (d i) (f i) = 1) :
    MvPowerSeries.coeff (∑ i ∈ s, d i) (∏ i ∈ s, f i) = 1 := by
  classical
  rw [MvPowerSeries.coeff_prod]
  let e : ι →₀ (σ →₀ ℕ) := ∑ i ∈ s, Finsupp.single i (d i)
  have he_mem : e ∈ Finset.finsuppAntidiag s (∑ i ∈ s, d i) := by
    simp only [Finset.mem_finsuppAntidiag]
    constructor
    · calc
        (∑ x ∈ s, e x) =
            ∑ x ∈ s, ∑ c ∈ s, (Finsupp.single c (d c)) x := by
              simp only [e, Finsupp.finset_sum_apply]
        _ = ∑ c ∈ s, ∑ x ∈ s, (Finsupp.single c (d c)) x := by
              rw [Finset.sum_comm]
        _ = ∑ c ∈ s, d c := by
              apply Finset.sum_congr rfl
              intro c hc
              simp [Finsupp.single_apply, hc]
    · intro x hx
      by_contra hxs
      have hz : e x = 0 := by
        simp only [e, Finsupp.finset_sum_apply]
        apply Finset.sum_eq_zero
        intro i hi
        have hix : i ≠ x := by
          intro h
          exact hxs (h ▸ hi)
        simp [Finsupp.single_apply, hix]
      exact (Finsupp.mem_support_iff.mp hx) hz
  have heval : ∀ i ∈ s, e i = d i := by
    intro i hi
    calc
      e i = ∑ c ∈ s, (Finsupp.single c (d c)) i := by
        simp only [e, Finsupp.finset_sum_apply]
      _ = (Finsupp.single i (d i)) i := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          simp [Finsupp.single_apply, hji]
        · intro hnot
          exact False.elim (hnot hi)
      _ = d i := by simp
  have hmain :
      (∑ l ∈ Finset.finsuppAntidiag s (∑ i ∈ s, d i),
        ∏ i ∈ s, MvPowerSeries.coeff (l i) (f i)) =
      (∏ i ∈ s, MvPowerSeries.coeff (e i) (f i)) := by
    apply Finset.sum_eq_single e
    · intro l hl hne
      by_contra hprod
      have hsum : Finset.sum s l = ∑ i ∈ s, d i :=
        (Finset.mem_finsuppAntidiag.mp hl).1
      have hle : ∀ i ∈ s, l i ≤ d i := by
        intro i hi
        apply hsupport i hi (l i)
        intro hz
        apply hprod
        exact Finset.prod_eq_zero hi hz
      have hcoords : ∀ i ∈ s, l i = e i := by
        intro i hi
        have hsum' : Finset.sum s (fun j => l j) = Finset.sum s (fun j => d j) := by
          simpa using hsum
        have h := (Finset.sum_eq_sum_iff_of_le (fun j hj => hle j hj)).mp hsum' i hi
        rw [heval i hi]
        exact h
      have hsupport_l : l.support ⊆ s := (Finset.mem_finsuppAntidiag.mp hl).2
      have heq : l = e := by
        apply Finsupp.ext
        intro i
        by_cases hi : i ∈ s
        · exact hcoords i hi
        · have hli : l i = 0 := by
            by_contra hn
            exact hi (hsupport_l (Finsupp.mem_support_iff.mpr hn))
          have hei : e i = 0 := by
            simp only [e, Finsupp.finset_sum_apply]
            apply Finset.sum_eq_zero
            intro j hj
            have hji : j ≠ i := by
              intro h
              exact hi (h ▸ hj)
            simp [Finsupp.single_apply, hji]
          exact hli.trans hei.symm
      exact hne heq
    · intro h
      exact False.elim (h he_mem)
  rw [hmain]
  calc
    (∏ i ∈ s, MvPowerSeries.coeff (e i) (f i)) =
        ∏ i ∈ s, (1 : R) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [heval i hi, htop i hi]
    _ = 1 := by simp
