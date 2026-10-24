-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_power_integral_ennreal_ofReal_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:21:56.281598+00:00
-- url     : https://prove2.me/submissions/c7749cb1-74c5-4d0c-8b73-d602cfbc5303

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
open scoped BigOperators

theorem solution
    (n : Nat) (r : Real) (hr : 0 <= r) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Icc (0 : Real) r))
      (fun t : Real => ENNReal.ofReal ((r - t) ^ n / (Nat.factorial n : Real))) =
    ENNReal.ofReal (MeasureTheory.integral
      (MeasureTheory.volume.restrict (Set.Icc (0 : Real) r))
      (fun t : Real => (r - t) ^ n / (Nat.factorial n : Real))) := by
  let μ := MeasureTheory.volume.restrict (Set.Icc (0 : Real) r)
  let f : Real → Real := fun t => (r - t) ^ n / (Nat.factorial n : Real)
  have hnonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    dsimp [f]
    have hrt : 0 ≤ r - t := sub_nonneg.mpr ht.2
    positivity
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hfi : MeasureTheory.Integrable f μ := by
    simpa [μ, MeasureTheory.IntegrableOn] using
      (hcont.integrableOn_Icc (a := (0 : Real)) (b := r))
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hnonneg).symm