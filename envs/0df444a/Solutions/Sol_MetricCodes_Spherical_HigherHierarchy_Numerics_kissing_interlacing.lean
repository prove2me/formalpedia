-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Numerics.kissing_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/de8357e2-09f7-4a27-9bbb-0729b81b01de

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
    Interlacing kissingAmbient kissingStabilizer := by
  constructor
  · change 0 ≤ (0.00000249433171106134 : ℝ)
    norm_num
  · intro i
    fin_cases i <;> constructor <;> norm_num
end MetricCodes.Spherical.HigherHierarchy.Numerics
