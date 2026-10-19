-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.subst_support_witness
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:01:07.223272+00:00
-- url     : https://prove2.me/submissions/4ff82b2c-c04b-40a0-bc65-49c38cf29b42

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Algebra.BigOperators.Finsupp.Basic

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (sigma : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hsigma : ∀ i : Fin (m + 1), ∀ b : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff b (sigma i) ≠ 0 →
        q i ≤ ∑ j, q j * (b j : ℝ))
    (F : MvPowerSeries (Fin (m + 1)) ℂ) (a : Fin (m + 1) → ℕ)
    (ha : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (MvPowerSeries.subst sigma F) ≠ 0) :
    ∃ b : Fin (m + 1) → ℕ,
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) F ≠ 0 ∧
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (∏ i, sigma i ^ b i) ≠ 0 := by
  classical
  -- Positive weights exclude a nonzero constant term in every substituted series.
  have hconst (i : Fin (m + 1)) : MvPowerSeries.coeff 0 (sigma i) = 0 := by
    by_contra h
    have hwt := hsigma i 0 h
    simp only [Finsupp.zero_apply, Nat.cast_zero, mul_zero, Finset.sum_const_zero] at hwt
    exact (not_le_of_gt (hq i)) hwt
  have hsubst : MvPowerSeries.HasSubst sigma := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    exact hconst i
  -- If no exponent contributed, every term of the coefficient formula would vanish.
  have hsupport :
      ∃ d : Fin (m + 1) →₀ ℕ,
        MvPowerSeries.coeff d F ≠ 0 ∧
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (d.prod fun i n => sigma i ^ n) ≠ 0 := by
    by_contra hn
    apply ha
    rw [MvPowerSeries.coeff_subst hsubst F (InterpolationMatrix.exponentVector a)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hdF : MvPowerSeries.coeff d F = 0
    · rw [hdF, zero_smul]
    · have hdprod :
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
            (d.prod fun i n => sigma i ^ n) = 0 := by
        by_contra hne
        exact hn ⟨d, hdF, hne⟩
      rw [hdprod, smul_zero]
  obtain ⟨d, hdF, hdprod⟩ := hsupport
  refine ⟨Finsupp.equivFunOnFinite d, ?_, ?_⟩
  · simpa only [InterpolationMatrix.exponentVector, Equiv.symm_apply_apply] using hdF
  · rw [Finsupp.prod_pow] at hdprod
    exact hdprod