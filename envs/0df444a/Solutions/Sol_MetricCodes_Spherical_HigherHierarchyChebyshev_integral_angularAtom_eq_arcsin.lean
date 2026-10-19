-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.integral_angularAtom_eq_arcsin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/b0b93161-08bf-480c-b775-1a4b319ed5c2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_hasDerivAt_angularAntiderivative
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularAtom_continuous

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {R : ℝ} (hR : 0 < R) :
    (∫ t in (0 : ℝ)..1, angularAtom R t) =
      Real.arcsin (angularAmplitude R) / Real.pi := by
  have hint : IntervalIntegrable (angularAtom R)
      MeasureTheory.volume 0 1 :=
    (angularAtom_continuous hR).intervalIntegrable 0 1
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (angularAntiderivative R) (angularAtom R t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
    exact hasDerivAt_angularAntiderivative hR ht'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold angularAntiderivative
  simp [Real.sin_pi_div_two]
  ring
end MetricCodes.Spherical.HigherHierarchyChebyshev
