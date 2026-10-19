-- Prove2me | solution 1 for MetricCodes.Johnson.finite_bound_of_projection_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/eacd2de1-a365-44cb-a526-29ca1500a8e0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_projection_certificate
import Theorems.Thm_MetricCodes_Hamming_threshold_lt_one
import Theorems.Thm_MetricCodes_Johnson_threshold_lt_one
import Theorems.Thm_MetricCodes_Johnson_correlation_le_threshold_of_code

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution
    {n w p q L d : ℕ}
    (hdegree : AdmissibleDegrees n w p q L)
    (hd : 0 < d)
    (data : ProjectionGram n w p q L)
    (C : Finset (JohnsonSphere n w)) (hC : IsCode d C)
    (hgap : threshold n w d < topEigenvalue n w p q L) :
    (C.card : ℝ) ≤
      ((1 - threshold n w d) /
        (topEigenvalue n w p q L - threshold n w d)) *
          ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
            (MetricCodes.johnsonFibreDimension n w p q : ℝ)) := by
  apply MetricCodes.projection_certificate data.projections C
    correlation data.feature hdegree.fibreDimension_pos
    (threshold_lt_one hdegree.weight_pos hdegree.weight_lt hd) hgap
  · intro x _
    exact correlation_self x
  · intro x hx y hy hxy
    exact correlation_le_threshold_of_code hdegree.weight_pos
      hdegree.weight_lt hC hx hy hxy
  · intro x _ y _
    exact data.gram x y
end MetricCodes.Johnson
