-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.volume_preimage_smul
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:05:05.01649+00:00
-- url     : https://prove2.me/submissions/f00749ba-c437-40cd-8880-229940bcd99e

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory

theorem solution
    (m : Nat) (c : Real) (hc : 0 < c) (A : Set (Fin m → Real))
    (hA : MeasurableSet A) :
    MeasureTheory.volume ((fun x => c • x) ⁻¹' A) =
      ENNReal.ofReal (c⁻¹ ^ m) * MeasureTheory.volume A := by
  let f : (Fin m → Real) →ₗ[Real] (Fin m → Real) := c • LinearMap.id
  have hfdet : LinearMap.det f = c ^ m := by
    simp [f, LinearMap.det_smul]
  have hcoef : abs ((c ^ m)⁻¹) = c⁻¹ ^ m := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos hc _)), inv_pow]
  have hmap :
      Measure.map f volume =
        ENNReal.ofReal (c⁻¹ ^ m) • volume := by
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := f) (by
      rw [hfdet]
      exact pow_ne_zero _ (ne_of_gt hc))]
    rw [hfdet, hcoef]
  calc
    volume ((fun x : Fin m → Real => c • x) ⁻¹' A) =
        Measure.map f volume A := by
          change volume ((f : (Fin m → Real) → (Fin m → Real)) ⁻¹' A) =
            Measure.map f volume A
          exact (Measure.map_apply (LinearMap.continuous_on_pi f).measurable hA).symm
    _ = ENNReal.ofReal (c⁻¹ ^ m) * volume A := by
      rw [hmap]
      rfl