-- Prove2me | solution 2 for MazurTransfer.order13_no_noncuspidal_genus_two_point
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T05:28:25.400187+00:00
-- url     : https://prove2.me/submissions/6d7b28d3-c539-4f43-93fa-6d9f2430b8c6

import Mathlib
import Theorems.Thm_MazurProof_N13ConstructedRationalPointTheorem_affine_x_is_cuspidal

/-!
Reciprocal-coordinate reduction from the mission sextic to the existing
N13 affine-cuspidality theorem. The imported theorem remains an Open child.
This is a reduction; the imported child remains to be proved.
-/

/-- The reciprocal sextic has no rational noncuspidal affine point,
conditional on the imported N13 affine-cuspidality child. -/
theorem solution (x y : ℚ) (hx0 : x ≠ 0) (hxneg : x ≠ -1)
    (hcurve : y ^ 2 = x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 + 6 * x ^ 2 + 4 * x + 1) :
    False := by
  have key : MazurProof.N13CurveModel.C13SexticEq (x⁻¹) (y / x ^ 3) := by
    change (y / x ^ 3) ^ 2 =
      (x⁻¹) ^ 6 + 4 * (x⁻¹) ^ 5 + 6 * (x⁻¹) ^ 4 + 2 * (x⁻¹) ^ 3 +
        (x⁻¹) ^ 2 + 2 * x⁻¹ + 1
    rw [div_pow, hcurve]
    field_simp [hx0]
    <;> ring
  rcases MazurProof.N13ConstructedRationalPointTheorem.affine_x_is_cuspidal
      (x⁻¹) (y / x ^ 3) key with hzero | hneg
  · exact inv_ne_zero hx0 hzero
  · apply hxneg
    have hinv := congrArg (fun z : ℚ => z⁻¹) hneg
    simpa using hinv
