-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Numerics.log_scaled_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/e0d8ec26-85f2-4fc9-828e-f3e5bead40e2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy.Numerics
namespace MetricCodes.Spherical.HigherHierarchy.Numerics
theorem _root_.solution {u : ℝ} (hu : u ≠ 0) (k : ℕ) :
    Real.log u = Real.log ((2 : ℝ) ^ k * u) - k * Real.log 2 := by
  have h := Real.log_mul
    (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)) hu
  rw [Real.log_pow] at h
  linarith
end MetricCodes.Spherical.HigherHierarchy.Numerics
