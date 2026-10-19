-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Arcsine.beta_one_half_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/0024369b-2317-4c30-8c20-6d46d8cc8d27

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Interval
open MetricCodes.Spherical.HigherHierarchy.Arcsine
namespace MetricCodes.Spherical.HigherHierarchy.Arcsine
theorem _root_.solution :
    beta (1 : ℝ) (1 / 2 : ℝ) = 2 := by
  rw [beta, Real.Gamma_one]
  have hsum : (1 : ℝ) + 1 / 2 = 1 / 2 + 1 := by norm_num
  rw [hsum, Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.Gamma_one_half_eq]
  have hsqrt : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp
end MetricCodes.Spherical.HigherHierarchy.Arcsine
