-- Prove2me | solution 1 for MazurTransfer.order49_residual_orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_bounded_resultants
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T06:26:24.123136+00:00
-- url     : https://prove2.me/submissions/b6df626f-c4cd-4d6d-aca3-fa42f5b35f89

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Definitions.Def_MazurTransfer_OrderFortyNinePlaneTransferData
import Mathlib
import Theorems.Thm_MazurTransfer_order49_residual_orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction
import Theorems.Thm_MazurTransfer_order49_residual_polynomial_eval_obstruction_of_bounded_resultants
open Polynomial
theorem MazurTransfer.Order49ExistingG7FFromExactComponentHelpersUnusedScopesRepair.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.polynomial_eval_obstruction_of_bounded_resultants (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hres0 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0)
    (z : ℚ) :
    MazurTorsion.Kubert.orderSevenSelectionPolynomial d z ≠ 0 ∨
      ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).eval z ≠ 0 := by
  exact MazurTransfer.order49_residual_polynomial_eval_obstruction_of_bounded_resultants d hres0 hres1 hres2 z

theorem MazurTransfer.Order49ExistingG7FFromExactComponentHelpersUnusedScopesRepair.MazurTorsion.Kubert.orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hobstruction :
      MazurTorsion.Kubert.orderSevenSelectionPolynomial d (MazurTorsion.Kubert.orderSevenVeluX d x) ≠ 0 ∨
        ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7).eval
          (MazurTorsion.Kubert.orderSevenVeluX d x) ≠ 0) :
    MazurTorsion.Kubert.orderSevenG7F (MazurTorsion.Kubert.orderSevenFrickeParameter d)
        (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) = 0 := by
  exact MazurTransfer.order49_residual_orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction (d := d) (x := x) (y := y) hP hQ hkernel hobstruction
namespace MazurTransfer.Order49ExistingG7FFromExactComponentHelpersUnusedScopesRepair
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

open _root_.Polynomial
open _root_.Polynomial







end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

namespace MazurTorsion.Kubert

open OrderSevenBacktrackingCertificate



/-- Three nonzero bounded resultants discharge the nonbacktracking hypothesis
in the order-seven isogeny-tower equation for an order-`49` point. -/
theorem orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_bounded_resultants
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hres0 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0) :
    MazurTorsion.Kubert.orderSevenG7F (MazurTorsion.Kubert.orderSevenFrickeParameter d)
        (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) = 0 := by
  apply MazurTransfer.Order49ExistingG7FFromExactComponentHelpersUnusedScopesRepair.MazurTorsion.Kubert.orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction
    hP hQ hkernel
  exact MazurTransfer.Order49ExistingG7FFromExactComponentHelpersUnusedScopesRepair.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.polynomial_eval_obstruction_of_bounded_resultants
    d hres0 hres1 hres2 (MazurTorsion.Kubert.orderSevenVeluX d x)

end MazurTorsion.Kubert

end MazurTransfer.Order49ExistingG7FFromExactComponentHelpersUnusedScopesRepair

theorem solution {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hres0 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.selectionCofactor d) (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2 d) 33 7 ≠ 0) :
    MazurTorsion.Kubert.orderSevenG7F (MazurTorsion.Kubert.orderSevenFrickeParameter d)
        (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) = 0 := by
  exact MazurTransfer.Order49ExistingG7FFromExactComponentHelpersUnusedScopesRepair.MazurTorsion.Kubert.orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_bounded_resultants (d := d) (x := x) (y := y) hP hQ hkernel hres0 hres1 hres2
#print axioms solution
