-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.periodFunction_eq_analyticColumn_on_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:07:19.795014+00:00
-- url     : https://prove2.me/submissions/ccf8be0a-d187-4494-8229-a8479ef48bbe

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (j h : ℕ) (a A : Fin m → ℕ) :
    ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2),
      (((∏ i, (a i).choose (A i) : ℕ) : ℂ) * (1 + t) ^ h *
          (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
            Complex.log (1 + t)) ^ (∑ i, (a i - A i))) =
        analyticColumn h a A
          ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
            Complex.log (1 + t)) := by
  intro t ht
  have ht_norm : ‖t‖ = (1 / 2 : ℝ) := by
    simpa [Metric.mem_sphere, dist_eq_norm] using ht
  have ht_ne : 1 + t ≠ 0 := by
    intro hz
    have hsum : t + 1 = 0 := by simpa [add_comm] using hz
    have ht_eq : t = -1 := (add_eq_zero_iff_eq_neg.mp hsum)
    rw [ht_eq, norm_neg, norm_one] at ht_norm
    norm_num at ht_norm
  have hperiod : Complex.exp ((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    simpa using Complex.exp_nat_mul_two_pi_mul_I j
  have hexp :
      Complex.exp ((h : ℂ) *
        (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) + Complex.log (1 + t))) =
        (1 + t) ^ h := by
    calc
      Complex.exp ((h : ℂ) *
          (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) + Complex.log (1 + t))) =
          Complex.exp (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) +
            Complex.log (1 + t)) ^ h := by
              simpa using (Complex.exp_nat_mul
                (((j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) + Complex.log (1 + t)) h)
      _ = (1 + t) ^ h := by
        rw [Complex.exp_add, hperiod, one_mul, Complex.exp_log ht_ne]
  unfold analyticColumn
  rw [hexp]