-- Prove2me | solution 1 for MazurTransfer.order49_vertical_xNumeratorHomogeneous_directional
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:38:15.067376+00:00
-- url     : https://prove2.me/submissions/583698c2-1dc7-4859-a325-2df75ebf8889

import Definitions.Def_MazurTransfer_Order49DifferentialCertificateFormulas
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Mathlib
open Polynomial
namespace MazurTransfer.Order49DifferentialCertificateHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Doubling























/-- The directional numerator identity for tangent doubling.  Equivalently,
the derivative of `xNumeratorHomogeneous / (v * completedCubicHomogeneous)`
has numerator `2 * completedYNumeratorHomogeneous`. -/
theorem xNumeratorHomogeneous_directional
    (W : WeierstrassCurve ℚ) (u v du dv : ℚ) :
    MazurTorsion.Doubling.xNumeratorHomogeneousDirectional W u v du dv * v *
          MazurTorsion.Doubling.completedCubicHomogeneous W u v -
        MazurTorsion.Doubling.xNumeratorHomogeneous W u v *
          (dv * MazurTorsion.Doubling.completedCubicHomogeneous W u v +
            v * MazurTorsion.Doubling.completedCubicHomogeneousDirectional W u v du dv) =
      2 * MazurTorsion.Doubling.completedYNumeratorHomogeneous W u v * (du * v - u * dv) := by
  simp only [MazurTorsion.Doubling.xNumeratorHomogeneousDirectional,
    MazurTorsion.Doubling.completedCubicHomogeneous, MazurTorsion.Doubling.xNumeratorHomogeneous,
    MazurTorsion.Doubling.completedCubicHomogeneousDirectional,
    MazurTorsion.Doubling.completedYNumeratorHomogeneous]
  linear_combination
    -2 * u ^ 2 * v ^ 4 * (du * v - dv * u) * W.b_relation







end MazurTorsion.Doubling

end
end MazurTransfer.Order49DifferentialCertificateHelpers

theorem solution (W : WeierstrassCurve ℚ) (u v du dv : ℚ) :
    MazurTorsion.Doubling.xNumeratorHomogeneousDirectional W u v du dv * v *
          MazurTorsion.Doubling.completedCubicHomogeneous W u v -
        MazurTorsion.Doubling.xNumeratorHomogeneous W u v *
          (dv * MazurTorsion.Doubling.completedCubicHomogeneous W u v +
            v * MazurTorsion.Doubling.completedCubicHomogeneousDirectional W u v du dv) =
      2 * MazurTorsion.Doubling.completedYNumeratorHomogeneous W u v * (du * v - u * dv) := by
  exact @MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Doubling.xNumeratorHomogeneous_directional W u v du dv
#print axioms solution
