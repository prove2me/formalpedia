-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneHalfLineProductIBP
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:20:11.560144+00:00
-- url     : https://prove2.me/submissions/5070a1ce-a29f-477f-b0c0-9b2eba5db3c3

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableCompensatedFourierNumeratorDerivative
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneNegativePowerAntiderivative
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneCompensatedProductIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneDerivativeProductIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneProductBoundaryZero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) *
          (((r ^ (-(alpha + 1)) : ℝ)) : ℂ) ∂volume) =
      -(∫ r in Set.Ioi (0 : ℝ),
        (Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ) ∂volume) := by
  let u : ℝ → ℂ := fun r =>
    Complex.exp (Complex.I * (r : ℂ)) - 1 - Complex.I * (r : ℂ)
  let v : ℝ → ℂ := fun r => ((r ^ (-alpha) / (-alpha) : ℝ) : ℂ)
  let u' : ℝ → ℂ := fun r =>
    Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)
  let v' : ℝ → ℂ := fun r => ((r ^ (-(alpha + 1)) : ℝ) : ℂ)
  have hu : ∀ r ∈ Set.Ioi (0 : ℝ), HasDerivAt u (u' r) r := by
    intro r hr
    exact Kyprianou.Ch01.stableCompensatedFourierNumeratorDerivative r
  have hv : ∀ r ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' r) r := by
    intro r hr
    exact (Kyprianou.Ch01.stableAlphaAboveOneNegativePowerAntiderivative
      alpha r ha1 ha2 hr).ofReal_comp
  have hprod : IntegrableOn (u * v') (Set.Ioi (0 : ℝ)) :=
    Kyprianou.Ch01.stableAlphaAboveOneCompensatedProductIntegrable
      alpha ha1 ha2
  have hother : IntegrableOn (u' * v) (Set.Ioi (0 : ℝ)) :=
    Kyprianou.Ch01.stableAlphaAboveOneDerivativeProductIntegrable
      alpha ha1 ha2
  obtain ⟨hzero, hinfty⟩ :=
    Kyprianou.Ch01.stableAlphaAboveOneProductBoundaryZero
      alpha ha1 ha2
  have h := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (u := u) (v := v) (u' := u') (v' := v')
    hu hv hprod hother hzero hinfty
  simpa only [u, v, u', v', Pi.mul_apply, sub_zero, zero_sub] using h
