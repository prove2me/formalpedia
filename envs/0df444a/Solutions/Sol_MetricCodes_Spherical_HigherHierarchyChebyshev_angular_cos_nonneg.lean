-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.angular_cos_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/828679bc-5fc4-4641-a3bf-d4baf362ba9e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped Interval
open MetricCodes MetricCodes.Spherical MetricCodes.Spherical.HigherHierarchyChebyshev
namespace MetricCodes.Spherical.HigherHierarchyChebyshev
theorem _root_.solution {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ Real.cos (Real.pi * t / 2) := by
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · nlinarith [Real.pi_pos, ht.1]
  · nlinarith [Real.pi_pos, ht.2]
end MetricCodes.Spherical.HigherHierarchyChebyshev
