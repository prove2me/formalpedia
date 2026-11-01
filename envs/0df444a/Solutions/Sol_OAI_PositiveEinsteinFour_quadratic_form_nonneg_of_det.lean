-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.quadratic_form_nonneg_of_det
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T18:46:04.968313+00:00
-- url     : https://prove2.me/submissions/eac619d2-d0ba-428f-8c46-5edd43c18d77

import Mathlib

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small positive semidefinite forms and Schur completion

The closed determinant criterion includes vanishing diagonal entries. The
Schur estimate below consequently includes the singular axial endpoint of the
quadratic comparison in Section 6 of the manuscript.
-/

namespace PositiveEinsteinFour

/-- The determinant test for a symmetric two-by-two real quadratic form,
including zero diagonal entries. -/
theorem quadratic_form_nonneg_of_det_oai
    (r h s : ℝ) (hr : 0 ≤ r) (hh : 0 ≤ h) (hdet : s ^ 2 ≤ r * h)
    (x y : ℝ) :
    0 ≤ r * x ^ 2 + 2 * s * x * y + h * y ^ 2 := by
  by_cases hrzero : r = 0
  · have hs : s = 0 := by nlinarith [sq_nonneg s]
    subst r
    subst s
    simpa using mul_nonneg hh (sq_nonneg y)
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
    have hdet_y : 0 ≤ (r * h - s ^ 2) * y ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hdet) (sq_nonneg y)
    have hidentity :
        r * (r * x ^ 2 + 2 * s * x * y + h * y ^ 2) =
          (r * x + s * y) ^ 2 + (r * h - s ^ 2) * y ^ 2 := by ring
    have hproduct : 0 ≤ r * (r * x ^ 2 + 2 * s * x * y + h * y ^ 2) := by
      rw [hidentity]
      exact add_nonneg (sq_nonneg _) hdet_y
    exact nonneg_of_mul_nonneg_right hproduct hrpos

end PositiveEinsteinFour

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.quadratic_form_nonneg_of_det_oai := @OAI.PositiveEinsteinFour.quadratic_form_nonneg_of_det_oai
