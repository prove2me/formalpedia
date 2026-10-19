-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.hasDerivAt_angularAntiderivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/dfb7039f-4aff-4ebd-821e-8fe127400efc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularAtom_eq
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularAmplitude_sin_mem
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularAmplitude_sqrt_complement

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (angularAntiderivative R) (angularAtom R t) t := by
  have harg := angularAmplitude_sin_mem hR t
  have hlin : HasDerivAt (fun x : ℝ => Real.pi * x / 2)
      (Real.pi / 2) t := by
    simpa using ((hasDerivAt_id t).const_mul Real.pi).div_const 2
  have hinner :
      HasDerivAt
        (fun x : ℝ => angularAmplitude R * Real.sin (Real.pi * x / 2))
        (angularAmplitude R *
          (Real.cos (Real.pi * t / 2) * (Real.pi / 2))) t := by
    simpa [Function.comp_def] using
      (((Real.hasDerivAt_sin (Real.pi * t / 2)).comp t hlin).const_mul
        (angularAmplitude R))
  have harc := (Real.hasDerivAt_arcsin
    (ne_of_gt harg.1) (ne_of_lt harg.2)).comp t hinner
  have hderiv := harc.const_mul (1 / Real.pi)
  have hformula :
      (1 / Real.pi) *
        (1 / Real.sqrt
            (1 - (angularAmplitude R * Real.sin (Real.pi * t / 2)) ^ 2) *
          (angularAmplitude R *
            (Real.cos (Real.pi * t / 2) * (Real.pi / 2)))) =
        angularAtom R t := by
    rw [angularAtom_eq hR ht,
      angularAmplitude_sqrt_complement hR t]
    unfold angularAmplitude
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hD : Real.sqrt (1 + 4 * R) ≠ 0 := by positivity
    have hA : Real.sqrt
        (1 + 4 * R * Real.cos (Real.pi * t / 2) ^ 2) ≠ 0 := by positivity
    field_simp
  rw [hformula] at hderiv
  change HasDerivAt
    (fun x : ℝ => (1 / Real.pi) *
      Real.arcsin (angularAmplitude R * Real.sin (Real.pi * x / 2)))
    (angularAtom R t) t
  simpa only [Function.comp_apply] using hderiv
end MetricCodes.Spherical.HigherHierarchyChebyshev
