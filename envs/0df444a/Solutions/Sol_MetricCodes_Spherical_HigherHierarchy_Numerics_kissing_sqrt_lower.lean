-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_sqrt_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/d1bc77e5-be3e-4104-9859-4f3160dd74b2

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
theorem _root_.solution :
    (0.31420830982168 : ℝ) <
        Real.sqrt (quadraticCoordinate (kissingAmbient 0)) ∧
      (0.02379658538854 : ℝ) <
        Real.sqrt (quadraticCoordinate (kissingAmbient 1)) ∧
      (0.00157934731226 : ℝ) <
        Real.sqrt (quadraticCoordinate (kissingAmbient 2)) := by
  constructor
  · apply Real.lt_sqrt_of_sq_lt
    norm_num [quadraticCoordinate]
  constructor
  · apply Real.lt_sqrt_of_sq_lt
    norm_num [quadraticCoordinate]
  · apply Real.lt_sqrt_of_sq_lt
    norm_num [quadraticCoordinate]
end MetricCodes.Spherical.HigherHierarchy.Numerics
