-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.angularAtom_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/90e05a04-1c7d-49a5-b614-d92411308e7d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_spectralAtom_inverseQuadratic
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularQuadratic_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_angularQuadratic_eq_cos_half_sq
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_sqrt_angularQuadratic

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
    angularAtom R t =
      Real.sqrt R * Real.cos (Real.pi * t / 2) /
        Real.sqrt (1 + 4 * R * Real.cos (Real.pi * t / 2) ^ 2) := by
  unfold angularAtom
  rw [spectralAtom_inverseQuadratic
    (angularQuadratic_nonneg hR.le t)]
  rw [sqrt_angularQuadratic hR ht,
    angularQuadratic_eq_cos_half_sq]
  ring_nf
end MetricCodes.Spherical.HigherHierarchyChebyshev
