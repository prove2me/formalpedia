-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneShiftedSineIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:20:54.965106+00:00
-- url     : https://prove2.me/submissions/5d1e6a0f-f55a-42be-8220-eef175f8227a

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneSineKernelIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneImaginaryKernelScalingPointwise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! Scale the Proved integrable source sine phase to its shifted cutoff. -/
theorem solution
    (z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun u : ℝ => (u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  let f : ℝ → ℝ := fun u => (u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2
  have hG := Kyprianou.Ch01.stableAlphaOneSineKernelIntegrable z hz
  have heq :
      (fun r : ℝ => z ^ 2 * f (z * r)) =
      (fun r : ℝ => ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2) := by
    funext r
    exact (Kyprianou.Ch01.stableAlphaOneImaginaryKernelScalingPointwise z r hz).symm
  have hScaled : IntegrableOn (fun r : ℝ => z ^ 2 * f (z * r))
      (Set.Ioi (0 : ℝ)) := by
    rw [heq]
    exact hG
  have hInv := hScaled.const_mul ((z ^ 2)⁻¹)
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  have hComp : IntegrableOn (fun r : ℝ => f (z * r))
      (Set.Ioi (0 : ℝ)) := by
    change Integrable (fun r : ℝ => f (z * r))
      (volume.restrict (Set.Ioi (0 : ℝ)))
    simpa [hz2, mul_assoc] using hInv
  have hTarget :=
    (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff f 0 hz).mp hComp
  simpa only [mul_zero] using hTarget
