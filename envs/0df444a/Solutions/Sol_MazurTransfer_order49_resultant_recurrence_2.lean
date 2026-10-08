-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence_2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T10:26:13.571578+00:00
-- url     : https://prove2.me/submissions/af16f432-83e3-468e-af3c-2edf03a05c63

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData1
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData2
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_MazurTransfer_order49_scalarResidual2Coefficient0_parametric_exact_certificate
import Theorems.Thm_MazurTransfer_order49_scalarResidual2Coefficient1_parametric_exact_certificate
import Theorems.Thm_MazurTransfer_order49_scalarResidual2Coefficient2_parametric_exact_certificate
import Theorems.Thm_MazurTransfer_order49_scalarResidual2Coefficient3_parametric_exact_certificate
import Theorems.Thm_MazurTransfer_order49_scalarResidual2Coefficient4_parametric_exact_certificate
open Polynomial
theorem ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.scalarResidual2Coefficient0 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 ^ 2 *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient0 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional2 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient0 := by
  exact MazurTransfer.order49_scalarResidual2Coefficient0_parametric_exact_certificate.identity

theorem ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.scalarResidual2Coefficient1 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 ^ 2 *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient0 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6) +
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient1 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional2 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient1 := by
  exact MazurTransfer.order49_scalarResidual2Coefficient1_parametric_exact_certificate.identity

theorem ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.scalarResidual2Coefficient2 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 ^ 2 *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient1 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6) +
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient2 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional2 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient2 := by
  exact MazurTransfer.order49_scalarResidual2Coefficient2_parametric_exact_certificate.identity

theorem ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.scalarResidual2Coefficient3 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 ^ 2 *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient2 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6) +
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient3 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional2 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient3 := by
  exact MazurTransfer.order49_scalarResidual2Coefficient3_parametric_exact_certificate.identity

theorem ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.scalarResidual2Coefficient4 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 ^ 2 *
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient3 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6) +
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional2 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4 := by
  exact MazurTransfer.order49_scalarResidual2Coefficient4_parametric_exact_certificate.identity

namespace ScalarRecurrence2
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private def sextic
    (a0 a1 a2 a3 a4 a5 a6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Bivariate :=
  C a6 * X ^ 6 + C a5 * X ^ 5 + C a4 * X ^ 4 +
    C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0

private def quintic
    (b0 b1 b2 b3 b4 b5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Bivariate :=
  C b5 * X ^ 5 + C b4 * X ^ 4 + C b3 * X ^ 3 +
    C b2 * X ^ 2 + C b1 * X + C b0

private def quartic
    (c0 c1 c2 c3 c4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Bivariate :=
  C c4 * X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 +
    C c1 * X + C c0

private def quotientDerived
    (a5 a6 b4 b5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient) : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Bivariate :=
  C (b5 * a6) * X + C (b5 * a5 - b4 * a6)

private theorem sextic_quintic_pseudodivision
    (a0 a1 a2 a3 a4 a5 a6 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient)
    (b0 b1 b2 b3 b4 b5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient)
    (c0 c1 c2 c3 c4 exceptional : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient)
    (residual0 : b5 ^ 2 * a0 =
      b0 * (b5 * a5 - b4 * a6) +
        a6 ^ 2 * exceptional * c0)
    (residual1 : b5 ^ 2 * a1 =
      b0 * (b5 * a6) +
      b1 * (b5 * a5 - b4 * a6) +
        a6 ^ 2 * exceptional * c1)
    (residual2 : b5 ^ 2 * a2 =
      b1 * (b5 * a6) +
      b2 * (b5 * a5 - b4 * a6) +
        a6 ^ 2 * exceptional * c2)
    (residual3 : b5 ^ 2 * a3 =
      b2 * (b5 * a6) +
      b3 * (b5 * a5 - b4 * a6) +
        a6 ^ 2 * exceptional * c3)
    (residual4 : b5 ^ 2 * a4 =
      b3 * (b5 * a6) +
      b4 * (b5 * a5 - b4 * a6) +
        a6 ^ 2 * exceptional * c4)
    : C (b5 ^ 2) * ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.sextic a0 a1 a2 a3 a4 a5 a6 =
      ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quintic b0 b1 b2 b3 b4 b5 *
          ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotientDerived a5 a6 b4 b5 +
        C (a6 ^ 2 * exceptional) * ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quartic c0 c1 c2 c3 c4 := by
  unfold ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.sextic ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quintic ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quartic ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotientDerived
  have mapped0 := congrArg C residual0
  have mapped1 := congrArg C residual1
  have mapped2 := congrArg C residual2
  have mapped3 := congrArg C residual3
  have mapped4 := congrArg C residual4
  simp only [map_mul, map_pow, map_add, map_sub] at mapped0 mapped1 mapped2 mapped3 mapped4
  simp only [map_mul, map_pow, map_sub]
  linear_combination mapped0 + mapped1 * X + mapped2 * X ^ 2 +
    mapped3 * X ^ 3 + mapped4 * X ^ 4











private theorem remainder2_coefficient5 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2.coeff 5 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm
  simp

private theorem remainder2_coefficient6 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2.coeff 6 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm
  simp









private theorem remainder3_coefficient4 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3.coeff 4 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm
  simp

private theorem remainder3_coefficient5 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3.coeff 5 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm
  simp











theorem recurrence2_checked : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence2 := by
  have division := ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.sextic_quintic_pseudodivision
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient0 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient1
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient4 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient3 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient5 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient0
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient1 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient2
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient3 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional2
    ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.scalarResidual2Coefficient0 ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.scalarResidual2Coefficient1
    ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.scalarResidual2Coefficient2 ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.scalarResidual2Coefficient3
    ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.scalarResidual2Coefficient4
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence2
  rw [ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3_coefficient5, ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coefficient6]
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotient2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.linearPseudoQuotient
  rw [ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coefficient5, ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2_coefficient6]
  rw [ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3_coefficient4, ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3_coefficient5]
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm
  unfold ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.sextic ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quintic ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quartic ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.quotientDerived at division
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4 MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.outerTerm
  linear_combination division

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end ScalarRecurrence2

theorem solution : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence2 := by
  exact ScalarRecurrence2.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence2_checked
#print axioms solution
