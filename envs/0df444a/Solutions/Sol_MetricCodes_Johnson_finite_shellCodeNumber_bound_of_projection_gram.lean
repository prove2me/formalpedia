-- Prove2me | solution 1 for MetricCodes.Johnson.finite_shellCodeNumber_bound_of_projection_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/e13af850-d27b-4c5a-8da8-d4d60f81999d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_finite_bound_of_projection_gram
import Theorems.Thm_MetricCodes_Johnson_exists_shellCodeNumber
import Theorems.Thm_MetricCodes_Johnson_card_asSubtype
import Theorems.Thm_MetricCodes_Johnson_isCode_asSubtype
import Theorems.Thm_MetricCodes_Johnson_finite_bound_of_projection_gram

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
    (hgap : threshold n w d < topEigenvalue n w p q L) :
    (shellCodeNumber n w d : ℝ) ≤
      ((1 - threshold n w d) /
        (topEigenvalue n w p q L - threshold n w d)) *
          ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
            (MetricCodes.johnsonFibreDimension n w p q : ℝ)) := by
  obtain ⟨C, hweight, hC, hcard⟩ := exists_shellCodeNumber n w d
  have hbound := finite_bound_of_projection_gram hdegree hd data
    (asSubtype C hweight) (isCode_asSubtype C hweight hC) hgap
  rw [card_asSubtype, hcard] at hbound
  exact hbound
end MetricCodes.Johnson
