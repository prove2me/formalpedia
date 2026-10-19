-- Prove2me | solution 1 for MetricCodes.Johnson.finite_binaryCodeNumber_bound_of_projection_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/29b8d0d8-f873-4a34-bbc6-a4ac30175035

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_bassalygo_elias_real
import Theorems.Thm_MetricCodes_Johnson_finite_shellCodeNumber_bound_of_projection_gram

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
    (binaryCodeNumber n d : ℝ) ≤
      ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (((1 - threshold n w d) /
          (topEigenvalue n w p q L - threshold n w d)) *
            ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
              (MetricCodes.johnsonFibreDimension n w p q : ℝ))) := by
  have hfactor : 0 ≤ (2 : ℝ) ^ n / (n.choose w : ℝ) := by
    exact div_nonneg (by positivity) (Nat.cast_nonneg _)
  calc
    (binaryCodeNumber n d : ℝ) ≤
        ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
          (shellCodeNumber n w d : ℝ) :=
      bassalygo_elias_real hdegree.weight_lt.le
    _ ≤ ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (((1 - threshold n w d) /
          (topEigenvalue n w p q L - threshold n w d)) *
            ((MetricCodes.johnsonAmbientDimension n (p + q) L : ℝ) /
              (MetricCodes.johnsonFibreDimension n w p q : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (finite_shellCodeNumber_bound_of_projection_gram
          hdegree hd data hgap)
        hfactor
end MetricCodes.Johnson
