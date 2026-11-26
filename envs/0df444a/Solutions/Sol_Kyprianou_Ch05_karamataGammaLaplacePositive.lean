-- Prove2me | solution 1 for Kyprianou.Ch05.karamataGammaLaplacePositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:44:28.556263+00:00
-- url     : https://prove2.me/submissions/76462c38-7817-4bf5-b9c8-4660429b4957

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Gamma-normalised power density has exact power Laplace transform. -/
theorem solution
    (rho t : Real) (hrho : 0 < rho) (ht : 0 < t) :
    positiveLaplace ((volume.restrict (Ioi (0 : Real))).withDensity
      (fun z : Real => ENNReal.ofReal (z^(rho-1)/Real.Gamma rho))) t =
      ENNReal.ofReal (t^(-rho)) := by
  have hg : 0 < Real.Gamma rho := Real.Gamma_pos_of_pos hrho
  have hKernel : (∫ x in Ioi (0 : Real), Real.exp (-(t*x))*x^(rho-1) ∂volume) =
      (1/t)^rho*Real.Gamma rho := by
    simpa only [mul_comm] using Real.integral_rpow_mul_exp_neg_mul_Ioi hrho ht
  have hkpos : 0 < (1/t)^rho*Real.Gamma rho :=
    mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr ht) _) hg
  have hi : IntegrableOn (fun x : Real => Real.exp (-(t*x))*x^(rho-1)) (Ioi 0) := by
    by_contra hn
    exact (ne_of_gt hkpos) (hKernel.symm.trans (integral_undef hn))
  have hdiv := hi.div_const (Real.Gamma rho)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : Real))]
      (fun x : Real => Real.exp (-(t*x))*x^(rho-1)/Real.Gamma rho) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx.le _)) hg.le
  unfold positiveLaplace
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  calc
    _ = ∫⁻ x in Ioi (0 : Real),
        ENNReal.ofReal (Real.exp (-(t*x))*x^(rho-1)/Real.Gamma rho) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hx.le _) hg.le)]
      congr 1
      ring
    _ = ENNReal.ofReal (∫ x in Ioi (0 : Real),
          Real.exp (-(t*x))*x^(rho-1)/Real.Gamma rho) :=
      (ofReal_integral_eq_lintegral_ofReal hdiv hnn).symm
    _ = _ := by rw [integral_div,hKernel,mul_div_cancel_right₀ _ hg.ne',
      one_div,Real.inv_rpow ht.le,Real.rpow_neg ht.le]
