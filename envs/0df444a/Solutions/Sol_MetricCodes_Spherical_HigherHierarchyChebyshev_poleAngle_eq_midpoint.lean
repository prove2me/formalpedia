-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.poleAngle_eq_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/90c6ffc2-3b7a-4271-aba6-cf7aa0298161

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {N : ℕ} (hN : 0 < N) (i : ℕ) :
    poleAngle N i = (((i : ℝ) + 1 / 2) * Real.pi) / (N : ℝ) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold poleAngle
  push_cast
  field_simp
end MetricCodes.Spherical.HigherHierarchyChebyshev
