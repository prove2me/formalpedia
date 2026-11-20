-- Prove2me | solution 1 for Kyprianou.Ch01.stableAboveOneUntruncatedPositiveIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:56:03.264196+00:00
-- url     : https://prove2.me/submissions/935e01ad-c181-4e9b-ad8e-cda3baa26ab0

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelIntegrable
open MeasureTheory Set Real Complex
set_option autoImplicit false
theorem solution
    (alpha xi : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (hxi : 0 < xi) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
          Complex.I * (((xi * r : ℝ) : ℂ))) /
          (((r ^ (alpha + 1) : ℝ) : ℂ)))
      (Set.Ioi (0 : ℝ)) := by
  let F : ℝ → ℂ := fun u =>
    (Complex.exp (Complex.I * (u : ℂ)) - 1 -
      Complex.I * (u : ℂ)) /
      (((u ^ (alpha + 1) : ℝ) : ℂ))
  have hu : IntegrableOn F (Set.Ioi (0 : ℝ)) := by
    simpa only [F] using
      Kyprianou.Ch01.stableAlphaAboveOneKernelIntegrable
        alpha ha1 ha2
  have hs : IntegrableOn (fun r : ℝ => F (xi * r))
      (Set.Ioi (0 : ℝ)) := by
    have hi := MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      F 0 hxi
    exact hi.mpr (by simpa only [mul_zero] using hu)
  have hmul (r : ℝ) (hr : 0 < r) :
      (xi * r) ^ (alpha + 1) =
        xi ^ (alpha + 1) * r ^ (alpha + 1) :=
    Real.mul_rpow hxi.le hr.le
  have hxpow : xi ^ (alpha + 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hxi _).ne'
  apply (IntegrableOn.congr_fun
    (hs.const_mul (((xi ^ (alpha + 1) : ℝ) : ℂ))) ?_ measurableSet_Ioi)
  · intro r hr
    dsimp [F]
    rw [hmul r hr]
    push_cast
    field_simp [hxpow, (Real.rpow_pos_of_pos hr _).ne']

