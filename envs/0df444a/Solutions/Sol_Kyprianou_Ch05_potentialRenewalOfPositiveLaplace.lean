-- Prove2me | solution 1 for Kyprianou.Ch05.potentialRenewalOfPositiveLaplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:21:34.128393+00:00
-- url     : https://prove2.me/submissions/f61a7422-6143-47a9-adce-2cb9e18b8f3a

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_measureEqOfFinitePositiveLaplace
import Theorems.Thm_Kyprianou_Ch05_renewalLaplaceGeometric
import Theorems.Thm_Kyprianou_Ch05_renewalResolventScalarIdentity
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- If the potential transforms are the unit-discounted and undiscounted resolvents of a strictly positive exponent, the renewal identity follows by uniqueness. -/
theorem solution
    (U : Real → Measure Real) [IsProbabilityMeasure (U 1)]
    (hLaplace : ∀ theta : Real, 0 < theta → ∃ a : Real, 0 < a ∧
        (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U 1)) = (ENNReal.ofReal (1 + a))⁻¹ ∧
        (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U 0)) = (ENNReal.ofReal a)⁻¹) :
    renewalMeasure (U 1) = Measure.dirac (0 : Real) + U 0 := by
  apply measureEqOfFinitePositiveLaplace
  · intro theta ht
    obtain ⟨a, ha, h1, h0⟩ := hLaplace theta ht
    rw [renewalLaplaceGeometric, h1, renewalResolventScalarIdentity a ha]
    apply ENNReal.add_lt_top.mpr
    exact ⟨by simp, by simpa [ENNReal.ofReal_eq_zero] using ha⟩
  · intro theta ht
    obtain ⟨a, ha, h1, h0⟩ := hLaplace theta ht
    rw [renewalLaplaceGeometric, h1, renewalResolventScalarIdentity a ha,
      lintegral_add_measure, h0]
    have hdirac :
        (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(Measure.dirac (0 : Real))) = 1 := by
      rw [lintegral_dirac]
      simp
    rw [hdirac]
