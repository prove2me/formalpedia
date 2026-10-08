-- Prove2me | solution 1 for MazurTransfer.order18_cubic_quotient_point_finite
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T14:38:51.315703+00:00
-- url     : https://prove2.me/submissions/42d53cdd-b590-4658-9608-fc86c077c3df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MazurTransfer_Order18RealCubicQuotientData
import Theorems.Thm_MazurTransfer_order18_real_cubic_quotient_isElliptic
import Theorems.Thm_MazurTransfer_order18_quotient_point_finite_of_surjective_doubling
import Theorems.Thm_MazurTransfer_order18_quotient_doubling_surjective
attribute [local instance] MazurTransfer.order18_real_cubic_quotient_isElliptic
open scoped WeierstrassCurve WeierstrassCurve.Affine
theorem solution : Finite MazurTorsion.XOneEighteenRealCubicQuotient.quotientCurve.toAffine.Point := by
  exact MazurTransfer.order18_quotient_point_finite_of_surjective_doubling
    MazurTransfer.order18_quotient_doubling_surjective
#print axioms solution
