-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_expanded
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:57:12.507248+00:00
-- url     : https://prove2.me/submissions/ef8bf750-e7e8-486e-a110-a1f4f295d3a1

import Mathlib.Algebra.Polynomial.Coeff
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_scalar
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData0. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial data for the order-seven branch-zero resultant PRS

This file starts the exact primitive pseudo-remainder sequence over
`ℚ[D][X]` for the selection cofactor and the first degree-seven
division cofactor. Each generated remainder is grouped by its outer
`X` coefficient; the first quotient remains exact table data, while
the later linear quotients are forced by the leading two coefficients.
Lean recurrence certificates check the untrusted generating computation.
-/
section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

noncomputable section






theorem coefficientTerm_eq_C_mul_X_pow
    (degree : ℕ) (coefficient : ℚ) :
    coefficientTerm degree coefficient =
      C coefficient * X ^ degree := by
  exact C_mul_X_pow_eq_monomial.symm





































































































































































































































































































































































































































































































































































































































































































































































end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData6. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Step 6 data for the order-seven branch-zero resultant PRS

This serial data shard records one normalized primitive remainder and
exceptional content factor. Its linear pseudo-division quotient is
derived from leading coefficients and checked by the Lean recurrence.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

noncomputable section

def remainder8Coefficient0Chunk0 : Coefficient :=
  coefficientTerm 0
    (-((1 : ℚ)))

def remainder8Coefficient0Block0 : Coefficient :=
  remainder8Coefficient0Chunk0

def remainder8Coefficient0 : Coefficient :=
  remainder8Coefficient0Block0

def remainder8 : Bivariate :=
  outerTerm 0 remainder8Coefficient0

def quotient6 : Bivariate :=
  linearPseudoQuotient
    remainder6 remainder7
    2 1

def exceptionalUnit6 : Coefficient :=
  C
    (((((((26813799997641 : ℚ) * 10 ^ 36 +
      142369575613846289747847827330896388) * 10 ^ 36 +
      174087143449204393900331622823388931) * 10 ^ 36 +
      504208118624079313576123579518587434) * 10 ^ 36 +
      856069465570511249870923189965244671) * 10 ^ 36 +
      650107475862081909428552923558342334) * 10 ^ 36 +
      248809782697354987477701994402490000)

def exceptional6 : Coefficient :=
  exceptionalUnit6 *
  (parameter - 1) ^ 1 *
  (discriminantFactor) ^ 6 *
  (cmTwelve) ^ 1

def recurrence6 : Prop :=
  C ((remainder7.coeff 1) ^ 2) *
      remainder6 =
    remainder7 * quotient6 +
      C ((remainder6.coeff 2) ^ 2 *
        exceptional6) * remainder8

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6ActualScalar. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: ActualScalar

This file is a checked arithmetic shard for the sixth pseudo-division
recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































theorem scalarResidual6 :
    remainder7Coefficient1 ^ 2 * remainder6Coefficient0 =
      remainder7Coefficient0 *
          (remainder7Coefficient1 * remainder6Coefficient1 -
            remainder7Coefficient0 * remainder6Coefficient2) -
        remainder6Coefficient2 ^ 2 * exceptional6 := by
  exact MazurTransfer.order49_resultant_recurrence6_scalar


end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The sixth order-seven branch-zero resultant recurrence

This file turns the checked scalar resultant identity into the bivariate
pseudo-division recurrence required by the backtracking certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private def quadratic
    (a0 a1 a2 : Coefficient) : Bivariate :=
  C a2 * X ^ 2 + C a1 * X + C a0

private def linear
    (b0 b1 : Coefficient) : Bivariate :=
  C b1 * X + C b0

private def quotientDerived
    (a1 a2 b0 b1 : Coefficient) : Bivariate :=
  C (b1 * a2) * X +
    C (b1 * a1 - b0 * a2)

private theorem quadratic_linear_pseudodivision
    (a0 a1 a2 b0 b1 exceptional : Coefficient)
    (residual :
      b1 ^ 2 * a0 =
        b0 * (b1 * a1 - b0 * a2) -
          a2 ^ 2 * exceptional) :
    C (b1 ^ 2) * quadratic a0 a1 a2 =
      linear b0 b1 * quotientDerived a1 a2 b0 b1 +
        C (a2 ^ 2 * exceptional) * (-1) := by
  unfold quadratic linear quotientDerived
  have mappedResidual := congrArg C residual
  simp only [map_mul, map_pow, map_sub] at mappedResidual
  simp only [map_mul, map_pow, map_sub]
  linear_combination mappedResidual



private theorem remainder6_coefficient1 :
    remainder6.coeff 1 = remainder6Coefficient1 := by
  unfold remainder6 outerTerm
  simp

private theorem remainder6_coefficient2 :
    remainder6.coeff 2 = remainder6Coefficient2 := by
  unfold remainder6 outerTerm
  simp

private theorem remainder7_coefficient0 :
    remainder7.coeff 0 = remainder7Coefficient0 := by
  unfold remainder7 outerTerm
  simp

private theorem remainder7_coefficient1 :
    remainder7.coeff 1 = remainder7Coefficient1 := by
  unfold remainder7 outerTerm
  simp

private theorem remainder8_eq :
    remainder8 = (-1 : Bivariate) := by
  unfold remainder8 remainder8Coefficient0
  unfold remainder8Coefficient0Block0 remainder8Coefficient0Chunk0
  unfold outerTerm
  rw [coefficientTerm_eq_C_mul_X_pow]
  norm_num

theorem recurrence6_checked : recurrence6 := by
  have division := quadratic_linear_pseudodivision
    remainder6Coefficient0
    remainder6Coefficient1
    remainder6Coefficient2
    remainder7Coefficient0
    remainder7Coefficient1
    exceptional6
    scalarResidual6
  unfold recurrence6
  rw [remainder6_coefficient2, remainder7_coefficient1]
  rw [remainder8_eq]
  unfold quotient6 linearPseudoQuotient
  rw [remainder6_coefficient1, remainder6_coefficient2]
  rw [remainder7_coefficient0, remainder7_coefficient1]
  unfold outerTerm
  unfold quadratic linear quotientDerived at division
  unfold remainder6 remainder7 outerTerm
  linear_combination division

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end

open Polynomial
open MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem solution :
C ((remainder7.coeff 1) ^ 2) * remainder6 =
  remainder7 * linearPseudoQuotient remainder6 remainder7 2 1 +
    C ((remainder6.coeff 2) ^ 2 * ((C
    (((((((26813799997641 : ℚ) * 10 ^ 36 +
      142369575613846289747847827330896388) * 10 ^ 36 +
      174087143449204393900331622823388931) * 10 ^ 36 +
      504208118624079313576123579518587434) * 10 ^ 36 +
      856069465570511249870923189965244671) * 10 ^ 36 +
      650107475862081909428552923558342334) * 10 ^ 36 +
      248809782697354987477701994402490000)) *
  (parameter - 1) ^ 1 *
  (discriminantFactor) ^ 6 *
  (cmTwelve) ^ 1)) * (-1 : Bivariate) := by
  have hr : remainder8 = (-1 : Bivariate) := by
    norm_num [remainder8, remainder8Coefficient0, remainder8Coefficient0Block0, remainder8Coefficient0Chunk0, outerTerm, coefficientTerm]
  simpa only [recurrence6, quotient6, exceptional6, exceptionalUnit6, hr] using recurrence6_checked

#print axioms solution
