-- Prove2me | solution 1 for Kyprianou.Ch05.unitExponentialClockMeanV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:38:44.096829+00:00
-- url     : https://prove2.me/submissions/069c1247-ec4a-4fca-86a5-f14cb61ddcc4


import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The nonnegative first moment of the unit-rate exponential clock is one. -/
theorem solution :
    (∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-t) * t) ∂volume) = 1 := by
  have he (t : Real) : Real.exp (-t) * t = Real.exp (-t) * t ^ ((2 : Real) - 1) := by
    norm_num
  have hi : IntegrableOn (fun t : Real => Real.exp (-t) * t) (Set.Ioi 0) := by
    simpa only [he] using Real.GammaIntegral_convergent (show (0 : Real) < 2 by norm_num)
  have hset : (volume : Measure Real).restrict (Set.Ici 0) =
      volume.restrict (Set.Ioi 0) := by
    apply Measure.restrict_congr_set
    exact Ioi_ae_eq_Ici.symm
  rw [hset]
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : Real))] (fun t => Real.exp (-t) * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_nonneg _) ht.le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  have h := Real.Gamma_eq_integral (show (0 : Real) < 2 by norm_num)
  rw [Real.Gamma_two] at h
  rw [show (∫ t in Set.Ioi (0 : Real), Real.exp (-t) * t) = 1 by
    simpa only [he] using h.symm]
  simp
