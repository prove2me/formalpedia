-- Prove2me | solution 1 for MetricCodes.Johnson.sqrt_one_sub_centeredDegree_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/9d16cb48-99bd-46d8-8283-fbea22cf654f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {u : ℝ}
    (hu : 0 < u) (hhalf : u < (1 : ℝ) / 2) :
    Real.sqrt (1 - centeredDegree u ^ 2) =
      2 * Real.sqrt (u * (1 - u)) := by
  have hvariance : 0 < u * (1 - u) :=
    mul_pos hu (by linarith)
  have hrad : 0 ≤ 1 - centeredDegree u ^ 2 := by
    unfold centeredDegree
    nlinarith
  have hsquare := Real.sq_sqrt hvariance.le
  apply (Real.sqrt_eq_iff_eq_sq hrad (by positivity)).mpr
  unfold centeredDegree
  nlinarith
end MetricCodes.Johnson
