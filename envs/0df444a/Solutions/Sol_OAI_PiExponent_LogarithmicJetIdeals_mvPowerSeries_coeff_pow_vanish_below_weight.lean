-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.mvPowerSeries_coeff_pow_vanish_below_weight
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T13:03:52.865815+00:00
-- url     : https://prove2.me/submissions/7208dd0d-e541-47e6-8d1e-850cfc382e12

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.ByContra
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {d : ℕ} (q : Fin d → ℝ) (rho : ℝ)
    (f : MvPowerSeries (Fin d) ℂ) (n : ℕ)
    (hq : ∀ j, 0 < q j)
    (hcoeff : ∀ a : Fin d → ℕ,
      (∑ j, q j * (a j : ℝ)) < rho →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm a) f = 0) :
    ∀ a : Fin d → ℕ,
      (∑ j, q j * (a j : ℝ)) < (n : ℝ) * rho →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm a) (f ^ n) = 0 := by
  classical
  intro a ha
  by_cases hn : n = 0
  · subst n
    have hnonneg : 0 ≤ ∑ j, q j * (a j : ℝ) := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (le_of_lt (hq j)) (Nat.cast_nonneg _)
    have ha' : (∑ j, q j * (a j : ℝ)) < 0 := by
      simpa only [Nat.cast_zero, zero_mul] using ha
    exact False.elim (not_lt_of_ge hnonneg ha')
  · rw [MvPowerSeries.coeff_pow]
    apply Finset.sum_eq_zero
    intro l hl
    have hsum : (∑ i ∈ Finset.range n, l i) =
        Finsupp.equivFunOnFinite.symm a :=
      (Finset.mem_finsuppAntidiag.mp hl).1
    have hparts (j : Fin d) : (∑ i ∈ Finset.range n, (l i) j) = a j := by
      have heval := congrArg (fun b : Fin d →₀ ℕ => b j) hsum
      simpa only [Finsupp.finsetSum_apply, Finsupp.coe_equivFunOnFinite_symm]
        using heval
    have hmass :
        (∑ i ∈ Finset.range n, ∑ j, q j * ((l i) j : ℝ)) =
          ∑ j, q j * (a j : ℝ) := by
      calc
        (∑ i ∈ Finset.range n, ∑ j, q j * ((l i) j : ℝ)) =
            ∑ j, ∑ i ∈ Finset.range n, q j * ((l i) j : ℝ) :=
          Finset.sum_comm
        _ = ∑ j, q j * (a j : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.mul_sum, ← Nat.cast_sum, hparts j]
    have hsmall : ∃ i ∈ Finset.range n,
        (∑ j, q j * ((l i) j : ℝ)) < rho := by
      by_contra! h
      have hbound : (n : ℝ) * rho ≤
          ∑ i ∈ Finset.range n, ∑ j, q j * ((l i) j : ℝ) := by
        calc
          (n : ℝ) * rho = ∑ i ∈ Finset.range n, rho := by
            simp [nsmul_eq_mul]
          _ ≤ ∑ i ∈ Finset.range n, ∑ j, q j * ((l i) j : ℝ) :=
            Finset.sum_le_sum (fun i hi => h i hi)
      rw [hmass] at hbound
      exact (not_le_of_gt ha) hbound
    obtain ⟨i, hi, hsmall⟩ := hsmall
    have hzero : MvPowerSeries.coeff (l i) f = 0 := by
      simpa using hcoeff (Finsupp.equivFunOnFinite (l i)) hsmall
    exact Finset.prod_eq_zero hi hzero