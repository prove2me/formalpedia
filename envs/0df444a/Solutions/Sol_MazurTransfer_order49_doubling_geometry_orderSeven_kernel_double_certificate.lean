-- Prove2me | solution 1 for MazurTransfer.order49_doubling_geometry_orderSeven_kernel_double_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:50:32.059146+00:00
-- url     : https://prove2.me/submissions/7eb88b3b-d670-4206-b814-ed034fa295f3

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Mathlib
open Polynomial
namespace MazurTransfer.Order49DoublingGeometryHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert



























private theorem orderSeven_kernel_double_certificate (d x : ℚ) :
    let H := MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x
    let p := MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x
    p * (p - MazurTorsion.Kubert.orderSevenB d * H) * (p - MazurTorsion.Kubert.orderSevenC d * H) =
      MazurTorsion.Kubert.orderSevenKernelPolynomial d x *
        MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x := by
  simp only [MazurTorsion.Doubling.completedCubic, MazurTorsion.Doubling.xNumerator,
    MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator,
    MazurTorsion.Kubert.orderSevenFamily, MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC, MazurTorsion.Kubert.tateNormalCurve,
    MazurTorsion.Kubert.orderSevenKernelPolynomial, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring







































end MazurTorsion.Kubert

end MazurTransfer.Order49DoublingGeometryHelpers

theorem solution (d x : ℚ) :
    let H := MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x
    let p := MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x
    p * (p - MazurTorsion.Kubert.orderSevenB d * H) * (p - MazurTorsion.Kubert.orderSevenC d * H) =
      MazurTorsion.Kubert.orderSevenKernelPolynomial d x *
        MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x := by
  apply MazurTransfer.Order49DoublingGeometryHelpers.MazurTorsion.Kubert.orderSeven_kernel_double_certificate <;> assumption
#print axioms solution
