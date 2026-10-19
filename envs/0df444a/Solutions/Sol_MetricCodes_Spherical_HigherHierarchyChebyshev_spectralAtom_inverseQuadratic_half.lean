-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.spectralAtom_inverseQuadratic_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/8fca2b9f-a12f-4fb2-99ef-fc171ead7e74

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_spectralAtom_inverseQuadratic

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) :
    MetricCodes.Spherical.HigherHierarchy.spectralAtom
      (inverseQuadratic x) =
      (1 / 2 : ℝ) * Real.sqrt (x / (x + 1 / 4)) := by
  rw [spectralAtom_inverseQuadratic hx, Real.sqrt_div hx]
  have hrad : 1 + 4 * x = 4 * (x + 1 / 4) := by ring
  rw [hrad, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  ring
end MetricCodes.Spherical.HigherHierarchyChebyshev
