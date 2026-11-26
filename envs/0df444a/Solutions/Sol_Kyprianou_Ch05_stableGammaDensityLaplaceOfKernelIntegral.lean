-- Prove2me | solution 1 for Kyprianou.Ch05.stableGammaDensityLaplaceOfKernelIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:47:03.199048+00:00
-- url     : https://prove2.me/submissions/5cca9f71-ac45-4c26-af53-4d4beaee9397

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (alpha theta : Real) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (ht : 0 < theta)
    (hKernel : (∫ x in Set.Ioi (0 : Real),
      Real.exp (-(theta * x)) * x ^ (alpha - 1) ∂volume) =
      (1 / theta) ^ alpha * Real.Gamma alpha) :
    (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂
      ((volume.restrict (Set.Ioi (0 : Real))).withDensity
        (fun z : Real => ENNReal.ofReal (z ^ (alpha - 1) / Real.Gamma alpha)))) =
        (ENNReal.ofReal (theta ^ alpha))⁻¹ := by
  have hg : 0 < Real.Gamma alpha := Real.Gamma_pos_of_pos ha0
  have hkpos : 0 < (1 / theta) ^ alpha * Real.Gamma alpha :=
    mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr ht) _) hg
  have hi : IntegrableOn (fun x : Real =>
      Real.exp (-(theta*x)) * x ^ (alpha-1)) (Set.Ioi 0) := by
    by_contra hn
    exact (ne_of_gt hkpos) (hKernel.symm.trans (integral_undef hn))
  have hdiv := hi.div_const (Real.Gamma alpha)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : Real))]
      (fun x : Real => Real.exp (-(theta*x)) * x ^ (alpha-1) / Real.Gamma alpha) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx.le _)) hg.le
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  calc
    _ = ∫⁻ x in Set.Ioi (0 : Real),
        ENNReal.ofReal (Real.exp (-(theta*x)) * x ^ (alpha-1) / Real.Gamma alpha) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hx.le _) hg.le)]
      congr 1
      ring
    _ = ENNReal.ofReal (∫ x in Set.Ioi (0 : Real),
          Real.exp (-(theta*x)) * x ^ (alpha-1) / Real.Gamma alpha) :=
      (ofReal_integral_eq_lintegral_ofReal hdiv hnn).symm
    _ = (ENNReal.ofReal (theta ^ alpha))⁻¹ := by
      rw [integral_div, hKernel, mul_div_cancel_right₀ _ hg.ne',
        one_div, ← Real.rpow_neg_eq_inv_rpow, Real.rpow_neg ht.le,
        ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos ht alpha)]
