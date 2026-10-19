-- Prove2me | solution 1 for MetricCodes.Johnson.correlation_le_threshold_of_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/395f6bac-6e41-4c3d-9000-b7aad0f6223f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_correlation_le_threshold

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {n w d : ℕ}
    (hw : 0 < w) (hwn : w < n)
    {C : Finset (JohnsonSphere n w)} (hC : IsCode d C)
    {x y : JohnsonSphere n w}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    correlation x y ≤ threshold n w d := by
  apply correlation_le_threshold hw hwn
  apply hC (Finset.mem_image_of_mem Subtype.val hx)
    (Finset.mem_image_of_mem Subtype.val hy)
  intro hval
  exact hxy (Subtype.ext hval)
end MetricCodes.Johnson
