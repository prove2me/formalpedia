-- Prove2me | solution 1 for Kyprianou.Ch05.renewalLaplaceGeometric
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:18:33.822436+00:00
-- url     : https://prove2.me/submissions/1ed19091-28d7-4a16-bf35-d0d5db18d099

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_lintegral_conv
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_geometric_measure_sum
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The nonnegative Laplace transform of the sum of convolution powers of a probability measure is the extended-real geometric series, including the infinite boundary case. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F] (theta : Real) :
    (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(renewalMeasure F)) =
      (1 - (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(F)))⁻¹ := by
  have hpow (n : Nat) :
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(renewalConvolutionPower F n)) =
        (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(F)) ^ n := by
    induction n with
    | zero =>
      simp [renewalConvolutionPower, lintegral_dirac]
    | succ n ih =>
      change (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂((renewalConvolutionPower F n).conv F)) = _
      rw [AvramDividend.Classical.positiveLaplace_lintegral_conv, ih, pow_succ]
  have h := AvramDividend.Classical.positiveLaplace_geometric_measure_sum
    (renewalConvolutionPower F) theta
    (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(F)) 1 hpow
  simpa [renewalMeasure] using h
