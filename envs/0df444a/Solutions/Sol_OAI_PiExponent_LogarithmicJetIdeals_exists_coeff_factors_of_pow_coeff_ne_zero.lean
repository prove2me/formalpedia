-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.exists_coeff_factors_of_pow_coeff_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T17:30:31.651887+00:00
-- url     : https://prove2.me/submissions/93a32f22-88fa-441e-a45c-81651ea08db2

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    {m : ℕ} (F : MvPowerSeries (Fin (m + 1)) ℂ) (n : ℕ)
    (a : Fin (m + 1) → ℕ)
    (hcoeff : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (F ^ n) ≠ 0) :
    ∃ b : Fin n → Fin (m + 1) → ℕ,
      (∀ i : Fin n,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector (b i)) F ≠ 0) ∧
      (∑ i : Fin n, InterpolationMatrix.exponentVector (b i)) =
        InterpolationMatrix.exponentVector a := by
  classical
  have hprod :
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (∏ _i : Fin n, F) ≠ 0 := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hcoeff
  rw [MvPowerSeries.coeff_prod] at hprod
  obtain ⟨c, hc, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hprod
  have hsum : (∑ i : Fin n, c i) = InterpolationMatrix.exponentVector a :=
    (Finset.mem_finsuppAntidiag.mp hc).1
  refine ⟨fun i => Finsupp.equivFunOnFinite (c i), ?_, ?_⟩
  · intro i
    have hi : MvPowerSeries.coeff (c i) F ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hterm) i (Finset.mem_univ i)
    simpa only [InterpolationMatrix.exponentVector, Equiv.symm_apply_apply] using hi
  · simpa only [InterpolationMatrix.exponentVector, Equiv.symm_apply_apply] using hsum