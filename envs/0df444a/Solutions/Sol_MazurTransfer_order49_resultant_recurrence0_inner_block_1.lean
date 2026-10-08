-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence0_inner_block_1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:15:01.685955+00:00
-- url     : https://prove2.me/submissions/403771d1-c1b1-4124-9d3e-16341cb6c035

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Mathlib.Tactic.Ring


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


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart1. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial resultant recurrence certificates for order-seven branch zero

This internal proof shard checks a balanced subset of the independent
coefficient identities used by the initial pseudo-remainder recurrence.
-/

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem recurrence0Inner6 :
    Internal.selectionCofactorCoefficient6 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient6 := by
  unfold Internal.selectionCofactorCoefficient6
    Internal.selectionCofactorCoefficient6Chunk8
    Internal.selectionCofactorCoefficient6Chunk7
    Internal.selectionCofactorCoefficient6Chunk6
    Internal.selectionCofactorCoefficient6Chunk5
    Internal.selectionCofactorCoefficient6Chunk4
    Internal.selectionCofactorCoefficient6Chunk3
    Internal.selectionCofactorCoefficient6Chunk2
    Internal.selectionCofactorCoefficient6Chunk1
    Internal.selectionCofactorCoefficient6Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient2
    quotient0Coefficient2Block0
    quotient0Coefficient2Chunk11
    quotient0Coefficient2Chunk10
    quotient0Coefficient2Chunk9
    quotient0Coefficient2Chunk8
    quotient0Coefficient2Chunk7
    quotient0Coefficient2Chunk6
    quotient0Coefficient2Chunk5
    quotient0Coefficient2Chunk4
    quotient0Coefficient2Chunk3
    quotient0Coefficient2Chunk2
    quotient0Coefficient2Chunk1
    quotient0Coefficient2Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient1
    quotient0Coefficient1Block0
    quotient0Coefficient1Chunk11
    quotient0Coefficient1Chunk10
    quotient0Coefficient1Chunk9
    quotient0Coefficient1Chunk8
    quotient0Coefficient1Chunk7
    quotient0Coefficient1Chunk6
    quotient0Coefficient1Chunk5
    quotient0Coefficient1Chunk4
    quotient0Coefficient1Chunk3
    quotient0Coefficient1Chunk2
    quotient0Coefficient1Chunk1
    quotient0Coefficient1Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient0
    quotient0Coefficient0Block1
    quotient0Coefficient0Block0
    quotient0Coefficient0Chunk12
    quotient0Coefficient0Chunk11
    quotient0Coefficient0Chunk10
    quotient0Coefficient0Chunk9
    quotient0Coefficient0Chunk8
    quotient0Coefficient0Chunk7
    quotient0Coefficient0Chunk6
    quotient0Coefficient0Chunk5
    quotient0Coefficient0Chunk4
    quotient0Coefficient0Chunk3
    quotient0Coefficient0Chunk2
    quotient0Coefficient0Chunk1
    quotient0Coefficient0Chunk0
    remainder2Coefficient6
    remainder2Coefficient6Block0
    remainder2Coefficient6Chunk11
    remainder2Coefficient6Chunk10
    remainder2Coefficient6Chunk9
    remainder2Coefficient6Chunk8
    remainder2Coefficient6Chunk7
    remainder2Coefficient6Chunk6
    remainder2Coefficient6Chunk5
    remainder2Coefficient6Chunk4
    remainder2Coefficient6Chunk3
    remainder2Coefficient6Chunk2
    remainder2Coefficient6Chunk1
    remainder2Coefficient6Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner7 :
    Internal.selectionCofactorCoefficient7 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient0 := by
  unfold Internal.selectionCofactorCoefficient7
    Internal.selectionCofactorCoefficient7Chunk8
    Internal.selectionCofactorCoefficient7Chunk7
    Internal.selectionCofactorCoefficient7Chunk6
    Internal.selectionCofactorCoefficient7Chunk5
    Internal.selectionCofactorCoefficient7Chunk4
    Internal.selectionCofactorCoefficient7Chunk3
    Internal.selectionCofactorCoefficient7Chunk2
    Internal.selectionCofactorCoefficient7Chunk1
    Internal.selectionCofactorCoefficient7Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient2
    quotient0Coefficient2Block0
    quotient0Coefficient2Chunk11
    quotient0Coefficient2Chunk10
    quotient0Coefficient2Chunk9
    quotient0Coefficient2Chunk8
    quotient0Coefficient2Chunk7
    quotient0Coefficient2Chunk6
    quotient0Coefficient2Chunk5
    quotient0Coefficient2Chunk4
    quotient0Coefficient2Chunk3
    quotient0Coefficient2Chunk2
    quotient0Coefficient2Chunk1
    quotient0Coefficient2Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient1
    quotient0Coefficient1Block0
    quotient0Coefficient1Chunk11
    quotient0Coefficient1Chunk10
    quotient0Coefficient1Chunk9
    quotient0Coefficient1Chunk8
    quotient0Coefficient1Chunk7
    quotient0Coefficient1Chunk6
    quotient0Coefficient1Chunk5
    quotient0Coefficient1Chunk4
    quotient0Coefficient1Chunk3
    quotient0Coefficient1Chunk2
    quotient0Coefficient1Chunk1
    quotient0Coefficient1Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient0
    quotient0Coefficient0Block1
    quotient0Coefficient0Block0
    quotient0Coefficient0Chunk12
    quotient0Coefficient0Chunk11
    quotient0Coefficient0Chunk10
    quotient0Coefficient0Chunk9
    quotient0Coefficient0Chunk8
    quotient0Coefficient0Chunk7
    quotient0Coefficient0Chunk6
    quotient0Coefficient0Chunk5
    quotient0Coefficient0Chunk4
    quotient0Coefficient0Chunk3
    quotient0Coefficient0Chunk2
    quotient0Coefficient0Chunk1
    quotient0Coefficient0Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner8 :
    Internal.selectionCofactorCoefficient8 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient1 := by
  unfold Internal.selectionCofactorCoefficient8
    Internal.selectionCofactorCoefficient8Chunk8
    Internal.selectionCofactorCoefficient8Chunk7
    Internal.selectionCofactorCoefficient8Chunk6
    Internal.selectionCofactorCoefficient8Chunk5
    Internal.selectionCofactorCoefficient8Chunk4
    Internal.selectionCofactorCoefficient8Chunk3
    Internal.selectionCofactorCoefficient8Chunk2
    Internal.selectionCofactorCoefficient8Chunk1
    Internal.selectionCofactorCoefficient8Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient8
    quotient0Coefficient8Block0
    quotient0Coefficient8Chunk8
    quotient0Coefficient8Chunk7
    quotient0Coefficient8Chunk6
    quotient0Coefficient8Chunk5
    quotient0Coefficient8Chunk4
    quotient0Coefficient8Chunk3
    quotient0Coefficient8Chunk2
    quotient0Coefficient8Chunk1
    quotient0Coefficient8Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient2
    quotient0Coefficient2Block0
    quotient0Coefficient2Chunk11
    quotient0Coefficient2Chunk10
    quotient0Coefficient2Chunk9
    quotient0Coefficient2Chunk8
    quotient0Coefficient2Chunk7
    quotient0Coefficient2Chunk6
    quotient0Coefficient2Chunk5
    quotient0Coefficient2Chunk4
    quotient0Coefficient2Chunk3
    quotient0Coefficient2Chunk2
    quotient0Coefficient2Chunk1
    quotient0Coefficient2Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient1
    quotient0Coefficient1Block0
    quotient0Coefficient1Chunk11
    quotient0Coefficient1Chunk10
    quotient0Coefficient1Chunk9
    quotient0Coefficient1Chunk8
    quotient0Coefficient1Chunk7
    quotient0Coefficient1Chunk6
    quotient0Coefficient1Chunk5
    quotient0Coefficient1Chunk4
    quotient0Coefficient1Chunk3
    quotient0Coefficient1Chunk2
    quotient0Coefficient1Chunk1
    quotient0Coefficient1Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner9 :
    Internal.selectionCofactorCoefficient9 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient2 := by
  unfold Internal.selectionCofactorCoefficient9
    Internal.selectionCofactorCoefficient9Chunk7
    Internal.selectionCofactorCoefficient9Chunk6
    Internal.selectionCofactorCoefficient9Chunk5
    Internal.selectionCofactorCoefficient9Chunk4
    Internal.selectionCofactorCoefficient9Chunk3
    Internal.selectionCofactorCoefficient9Chunk2
    Internal.selectionCofactorCoefficient9Chunk1
    Internal.selectionCofactorCoefficient9Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient9
    quotient0Coefficient9Block0
    quotient0Coefficient9Chunk8
    quotient0Coefficient9Chunk7
    quotient0Coefficient9Chunk6
    quotient0Coefficient9Chunk5
    quotient0Coefficient9Chunk4
    quotient0Coefficient9Chunk3
    quotient0Coefficient9Chunk2
    quotient0Coefficient9Chunk1
    quotient0Coefficient9Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient8
    quotient0Coefficient8Block0
    quotient0Coefficient8Chunk8
    quotient0Coefficient8Chunk7
    quotient0Coefficient8Chunk6
    quotient0Coefficient8Chunk5
    quotient0Coefficient8Chunk4
    quotient0Coefficient8Chunk3
    quotient0Coefficient8Chunk2
    quotient0Coefficient8Chunk1
    quotient0Coefficient8Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient2
    quotient0Coefficient2Block0
    quotient0Coefficient2Chunk11
    quotient0Coefficient2Chunk10
    quotient0Coefficient2Chunk9
    quotient0Coefficient2Chunk8
    quotient0Coefficient2Chunk7
    quotient0Coefficient2Chunk6
    quotient0Coefficient2Chunk5
    quotient0Coefficient2Chunk4
    quotient0Coefficient2Chunk3
    quotient0Coefficient2Chunk2
    quotient0Coefficient2Chunk1
    quotient0Coefficient2Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner10 :
    Internal.selectionCofactorCoefficient10 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient3 := by
  unfold Internal.selectionCofactorCoefficient10
    Internal.selectionCofactorCoefficient10Chunk7
    Internal.selectionCofactorCoefficient10Chunk6
    Internal.selectionCofactorCoefficient10Chunk5
    Internal.selectionCofactorCoefficient10Chunk4
    Internal.selectionCofactorCoefficient10Chunk3
    Internal.selectionCofactorCoefficient10Chunk2
    Internal.selectionCofactorCoefficient10Chunk1
    Internal.selectionCofactorCoefficient10Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient10
    quotient0Coefficient10Block0
    quotient0Coefficient10Chunk7
    quotient0Coefficient10Chunk6
    quotient0Coefficient10Chunk5
    quotient0Coefficient10Chunk4
    quotient0Coefficient10Chunk3
    quotient0Coefficient10Chunk2
    quotient0Coefficient10Chunk1
    quotient0Coefficient10Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient9
    quotient0Coefficient9Block0
    quotient0Coefficient9Chunk8
    quotient0Coefficient9Chunk7
    quotient0Coefficient9Chunk6
    quotient0Coefficient9Chunk5
    quotient0Coefficient9Chunk4
    quotient0Coefficient9Chunk3
    quotient0Coefficient9Chunk2
    quotient0Coefficient9Chunk1
    quotient0Coefficient9Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient8
    quotient0Coefficient8Block0
    quotient0Coefficient8Chunk8
    quotient0Coefficient8Chunk7
    quotient0Coefficient8Chunk6
    quotient0Coefficient8Chunk5
    quotient0Coefficient8Chunk4
    quotient0Coefficient8Chunk3
    quotient0Coefficient8Chunk2
    quotient0Coefficient8Chunk1
    quotient0Coefficient8Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient3
    quotient0Coefficient3Block0
    quotient0Coefficient3Chunk10
    quotient0Coefficient3Chunk9
    quotient0Coefficient3Chunk8
    quotient0Coefficient3Chunk7
    quotient0Coefficient3Chunk6
    quotient0Coefficient3Chunk5
    quotient0Coefficient3Chunk4
    quotient0Coefficient3Chunk3
    quotient0Coefficient3Chunk2
    quotient0Coefficient3Chunk1
    quotient0Coefficient3Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner11 :
    Internal.selectionCofactorCoefficient11 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient4 := by
  unfold Internal.selectionCofactorCoefficient11
    Internal.selectionCofactorCoefficient11Chunk7
    Internal.selectionCofactorCoefficient11Chunk6
    Internal.selectionCofactorCoefficient11Chunk5
    Internal.selectionCofactorCoefficient11Chunk4
    Internal.selectionCofactorCoefficient11Chunk3
    Internal.selectionCofactorCoefficient11Chunk2
    Internal.selectionCofactorCoefficient11Chunk1
    Internal.selectionCofactorCoefficient11Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient11
    quotient0Coefficient11Block0
    quotient0Coefficient11Chunk7
    quotient0Coefficient11Chunk6
    quotient0Coefficient11Chunk5
    quotient0Coefficient11Chunk4
    quotient0Coefficient11Chunk3
    quotient0Coefficient11Chunk2
    quotient0Coefficient11Chunk1
    quotient0Coefficient11Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient10
    quotient0Coefficient10Block0
    quotient0Coefficient10Chunk7
    quotient0Coefficient10Chunk6
    quotient0Coefficient10Chunk5
    quotient0Coefficient10Chunk4
    quotient0Coefficient10Chunk3
    quotient0Coefficient10Chunk2
    quotient0Coefficient10Chunk1
    quotient0Coefficient10Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient9
    quotient0Coefficient9Block0
    quotient0Coefficient9Chunk8
    quotient0Coefficient9Chunk7
    quotient0Coefficient9Chunk6
    quotient0Coefficient9Chunk5
    quotient0Coefficient9Chunk4
    quotient0Coefficient9Chunk3
    quotient0Coefficient9Chunk2
    quotient0Coefficient9Chunk1
    quotient0Coefficient9Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient8
    quotient0Coefficient8Block0
    quotient0Coefficient8Chunk8
    quotient0Coefficient8Chunk7
    quotient0Coefficient8Chunk6
    quotient0Coefficient8Chunk5
    quotient0Coefficient8Chunk4
    quotient0Coefficient8Chunk3
    quotient0Coefficient8Chunk2
    quotient0Coefficient8Chunk1
    quotient0Coefficient8Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient7
    quotient0Coefficient7Block0
    quotient0Coefficient7Chunk9
    quotient0Coefficient7Chunk8
    quotient0Coefficient7Chunk7
    quotient0Coefficient7Chunk6
    quotient0Coefficient7Chunk5
    quotient0Coefficient7Chunk4
    quotient0Coefficient7Chunk3
    quotient0Coefficient7Chunk2
    quotient0Coefficient7Chunk1
    quotient0Coefficient7Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient6
    quotient0Coefficient6Block0
    quotient0Coefficient6Chunk9
    quotient0Coefficient6Chunk8
    quotient0Coefficient6Chunk7
    quotient0Coefficient6Chunk6
    quotient0Coefficient6Chunk5
    quotient0Coefficient6Chunk4
    quotient0Coefficient6Chunk3
    quotient0Coefficient6Chunk2
    quotient0Coefficient6Chunk1
    quotient0Coefficient6Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient5
    quotient0Coefficient5Block0
    quotient0Coefficient5Chunk9
    quotient0Coefficient5Chunk8
    quotient0Coefficient5Chunk7
    quotient0Coefficient5Chunk6
    quotient0Coefficient5Chunk5
    quotient0Coefficient5Chunk4
    quotient0Coefficient5Chunk3
    quotient0Coefficient5Chunk2
    quotient0Coefficient5Chunk1
    quotient0Coefficient5Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient4
    quotient0Coefficient4Block0
    quotient0Coefficient4Chunk10
    quotient0Coefficient4Chunk9
    quotient0Coefficient4Chunk8
    quotient0Coefficient4Chunk7
    quotient0Coefficient4Chunk6
    quotient0Coefficient4Chunk5
    quotient0Coefficient4Chunk4
    quotient0Coefficient4Chunk3
    quotient0Coefficient4Chunk2
    quotient0Coefficient4Chunk1
    quotient0Coefficient4Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end

open Polynomial MazurTorsion.Kubert.OrderSevenBacktrackingCertificate MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem solution :
(Internal.selectionCofactorCoefficient6 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient6) ∧
(Internal.selectionCofactorCoefficient7 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient0) ∧
(Internal.selectionCofactorCoefficient8 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient1) ∧
(Internal.selectionCofactorCoefficient9 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient2) ∧
(Internal.selectionCofactorCoefficient10 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient3) ∧
(Internal.selectionCofactorCoefficient11 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient4) := by
  exact ⟨MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner6, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner7, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner8, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner9, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner10, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner11⟩

#print axioms solution
