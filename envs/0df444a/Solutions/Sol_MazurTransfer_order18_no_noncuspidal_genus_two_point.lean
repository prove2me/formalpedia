-- Prove2me | solution 1 for MazurTransfer.order18_no_noncuspidal_genus_two_point
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T14:19:53.663105+00:00
-- url     : https://prove2.me/submissions/50fa73ae-1cf5-4307-b1b9-37d57c8dbdde
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MazurTransfer_Order18RealCubicQuotientData
import Theorems.Thm_MazurTransfer_order18_real_cubic_quotient_isElliptic
import Theorems.Thm_MazurTransfer_order18_cubic_quotient_point_finite
import Theorems.Thm_MazurTransfer_order18_no_noncuspidal_of_finite_quotient
attribute [local instance] MazurTransfer.order18_real_cubic_quotient_isElliptic
open scoped WeierstrassCurve WeierstrassCurve.Affine

theorem solution (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve : y ^ 2 = x ^ 6 - 4 * x ^ 5 + 10 * x ^ 4 - 10 * x ^ 3 + 5 * x ^ 2 - 2 * x + 1) : False := by
  letI : Finite MazurTorsion.XOneEighteenRealCubicQuotient.quotientCurve.toAffine.Point :=
    MazurTransfer.order18_cubic_quotient_point_finite
  exact MazurTransfer.order18_no_noncuspidal_of_finite_quotient x y hx0 hx1 hcurve
#print axioms solution
