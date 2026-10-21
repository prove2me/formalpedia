-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_log_coeff_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:41:30.212753+00:00
-- url     : https://prove2.me/submissions/480838dc-1b4e-4ec2-9246-3d6525ef0e76

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_liftLogSeries_coeff_truncation
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

/-- Below the truncation cutoff, the lifted formal logarithm agrees coefficient-wise with its
finite Taylor sum: both coefficient functionals see only monomials in the distinguished variable,
and there the logarithm's Taylor coefficients coincide. -/
theorem solution {m : ℕ} (T : ℕ) (a : Fin (m + 1) →₀ ℕ) (ha : a 0 < T) :
    MvPowerSeries.coeff a (liftLogSeries m (PowerSeries.log ℂ)) =
      MvPowerSeries.coeff a
        (∑ k ∈ Finset.range T,
          (if k = 0 then 0 else
            (((-1 : ℂ) ^ (k + 1)) / (k : ℂ)) •
              (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) ℂ) ^ k)) := by
  classical
  -- finitely supported exponent vectors are the `exponentVector` of their values
  have haeq : a = OAI.PiExponent.InterpolationMatrix.exponentVector (fun j => a j) := by
    ext j
    simp [OAI.PiExponent.InterpolationMatrix.exponentVector]
  -- the already-proved truncation lemma compares with the finite sum of `C (log k) * X^k`
  have htr := OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_coeff_truncation
    m (PowerSeries.log ℂ) T (fun j => a j) ha
  change MvPowerSeries.coeff
      (OAI.PiExponent.InterpolationMatrix.exponentVector (fun j => a j))
      (liftLogSeries m (PowerSeries.log ℂ)) =
    MvPowerSeries.coeff
      (OAI.PiExponent.InterpolationMatrix.exponentVector (fun j => a j))
      (∑ n ∈ Finset.range T, MvPowerSeries.C (PowerSeries.coeff n (PowerSeries.log ℂ)) *
        (MvPowerSeries.X (0 : Fin (m + 1))) ^ n) at htr
  rw [← haeq] at htr
  rw [htr]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · have hc : (algebraMap ℚ ℂ) ((-1 : ℚ) ^ (k + 1) / (k : ℚ)) =
        ((-1 : ℂ) ^ (k + 1)) / (k : ℂ) := by
      push_cast
      ring
    rw [PowerSeries.coeff_log]
    simp only [if_neg hk0]
    rw [MvPowerSeries.smul_eq_C_mul, hc]
