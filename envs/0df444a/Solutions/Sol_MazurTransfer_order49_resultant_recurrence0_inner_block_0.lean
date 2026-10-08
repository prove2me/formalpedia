-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence0_inner_block_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:09:55.267893+00:00
-- url     : https://prove2.me/submissions/b74d09d0-3424-4bb7-92d7-50cd782be902

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


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart0. Original headers retained. -/
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

theorem recurrence0Inner0 :
    Internal.selectionCofactorCoefficient0 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient0 := by
  unfold Internal.selectionCofactorCoefficient0
    Internal.selectionCofactorCoefficient0Chunk10
    Internal.selectionCofactorCoefficient0Chunk9
    Internal.selectionCofactorCoefficient0Chunk8
    Internal.selectionCofactorCoefficient0Chunk7
    Internal.selectionCofactorCoefficient0Chunk6
    Internal.selectionCofactorCoefficient0Chunk5
    Internal.selectionCofactorCoefficient0Chunk4
    Internal.selectionCofactorCoefficient0Chunk3
    Internal.selectionCofactorCoefficient0Chunk2
    Internal.selectionCofactorCoefficient0Chunk1
    Internal.selectionCofactorCoefficient0Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
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
    remainder2Coefficient0
    remainder2Coefficient0Block1
    remainder2Coefficient0Block0
    remainder2Coefficient0Chunk14
    remainder2Coefficient0Chunk13
    remainder2Coefficient0Chunk12
    remainder2Coefficient0Chunk11
    remainder2Coefficient0Chunk10
    remainder2Coefficient0Chunk9
    remainder2Coefficient0Chunk8
    remainder2Coefficient0Chunk7
    remainder2Coefficient0Chunk6
    remainder2Coefficient0Chunk5
    remainder2Coefficient0Chunk4
    remainder2Coefficient0Chunk3
    remainder2Coefficient0Chunk2
    remainder2Coefficient0Chunk1
    remainder2Coefficient0Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner1 :
    Internal.selectionCofactorCoefficient1 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient1 := by
  unfold Internal.selectionCofactorCoefficient1
    Internal.selectionCofactorCoefficient1Chunk10
    Internal.selectionCofactorCoefficient1Chunk9
    Internal.selectionCofactorCoefficient1Chunk8
    Internal.selectionCofactorCoefficient1Chunk7
    Internal.selectionCofactorCoefficient1Chunk6
    Internal.selectionCofactorCoefficient1Chunk5
    Internal.selectionCofactorCoefficient1Chunk4
    Internal.selectionCofactorCoefficient1Chunk3
    Internal.selectionCofactorCoefficient1Chunk2
    Internal.selectionCofactorCoefficient1Chunk1
    Internal.selectionCofactorCoefficient1Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
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
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
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
    remainder2Coefficient1
    remainder2Coefficient1Block1
    remainder2Coefficient1Block0
    remainder2Coefficient1Chunk14
    remainder2Coefficient1Chunk13
    remainder2Coefficient1Chunk12
    remainder2Coefficient1Chunk11
    remainder2Coefficient1Chunk10
    remainder2Coefficient1Chunk9
    remainder2Coefficient1Chunk8
    remainder2Coefficient1Chunk7
    remainder2Coefficient1Chunk6
    remainder2Coefficient1Chunk5
    remainder2Coefficient1Chunk4
    remainder2Coefficient1Chunk3
    remainder2Coefficient1Chunk2
    remainder2Coefficient1Chunk1
    remainder2Coefficient1Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner2 :
    Internal.selectionCofactorCoefficient2 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient2 := by
  unfold Internal.selectionCofactorCoefficient2
    Internal.selectionCofactorCoefficient2Chunk9
    Internal.selectionCofactorCoefficient2Chunk8
    Internal.selectionCofactorCoefficient2Chunk7
    Internal.selectionCofactorCoefficient2Chunk6
    Internal.selectionCofactorCoefficient2Chunk5
    Internal.selectionCofactorCoefficient2Chunk4
    Internal.selectionCofactorCoefficient2Chunk3
    Internal.selectionCofactorCoefficient2Chunk2
    Internal.selectionCofactorCoefficient2Chunk1
    Internal.selectionCofactorCoefficient2Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
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
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
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
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
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
    remainder2Coefficient2
    remainder2Coefficient2Block1
    remainder2Coefficient2Block0
    remainder2Coefficient2Chunk13
    remainder2Coefficient2Chunk12
    remainder2Coefficient2Chunk11
    remainder2Coefficient2Chunk10
    remainder2Coefficient2Chunk9
    remainder2Coefficient2Chunk8
    remainder2Coefficient2Chunk7
    remainder2Coefficient2Chunk6
    remainder2Coefficient2Chunk5
    remainder2Coefficient2Chunk4
    remainder2Coefficient2Chunk3
    remainder2Coefficient2Chunk2
    remainder2Coefficient2Chunk1
    remainder2Coefficient2Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner3 :
    Internal.selectionCofactorCoefficient3 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient3 := by
  unfold Internal.selectionCofactorCoefficient3
    Internal.selectionCofactorCoefficient3Chunk9
    Internal.selectionCofactorCoefficient3Chunk8
    Internal.selectionCofactorCoefficient3Chunk7
    Internal.selectionCofactorCoefficient3Chunk6
    Internal.selectionCofactorCoefficient3Chunk5
    Internal.selectionCofactorCoefficient3Chunk4
    Internal.selectionCofactorCoefficient3Chunk3
    Internal.selectionCofactorCoefficient3Chunk2
    Internal.selectionCofactorCoefficient3Chunk1
    Internal.selectionCofactorCoefficient3Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
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
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
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
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
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
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
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
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
    remainder2Coefficient3Chunk13
    remainder2Coefficient3Chunk12
    remainder2Coefficient3Chunk11
    remainder2Coefficient3Chunk10
    remainder2Coefficient3Chunk9
    remainder2Coefficient3Chunk8
    remainder2Coefficient3Chunk7
    remainder2Coefficient3Chunk6
    remainder2Coefficient3Chunk5
    remainder2Coefficient3Chunk4
    remainder2Coefficient3Chunk3
    remainder2Coefficient3Chunk2
    remainder2Coefficient3Chunk1
    remainder2Coefficient3Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner4 :
    Internal.selectionCofactorCoefficient4 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient4 := by
  unfold Internal.selectionCofactorCoefficient4
    Internal.selectionCofactorCoefficient4Chunk9
    Internal.selectionCofactorCoefficient4Chunk8
    Internal.selectionCofactorCoefficient4Chunk7
    Internal.selectionCofactorCoefficient4Chunk6
    Internal.selectionCofactorCoefficient4Chunk5
    Internal.selectionCofactorCoefficient4Chunk4
    Internal.selectionCofactorCoefficient4Chunk3
    Internal.selectionCofactorCoefficient4Chunk2
    Internal.selectionCofactorCoefficient4Chunk1
    Internal.selectionCofactorCoefficient4Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
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
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
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
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
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
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
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
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
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
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner5 :
    Internal.selectionCofactorCoefficient5 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient5 := by
  unfold Internal.selectionCofactorCoefficient5
    Internal.selectionCofactorCoefficient5Chunk9
    Internal.selectionCofactorCoefficient5Chunk8
    Internal.selectionCofactorCoefficient5Chunk7
    Internal.selectionCofactorCoefficient5Chunk6
    Internal.selectionCofactorCoefficient5Chunk5
    Internal.selectionCofactorCoefficient5Chunk4
    Internal.selectionCofactorCoefficient5Chunk3
    Internal.selectionCofactorCoefficient5Chunk2
    Internal.selectionCofactorCoefficient5Chunk1
    Internal.selectionCofactorCoefficient5Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
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
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
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
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
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
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
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
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
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
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
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
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    exceptional0
    exceptionalUnit0
    parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end

open Polynomial MazurTorsion.Kubert.OrderSevenBacktrackingCertificate MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem solution :
(Internal.selectionCofactorCoefficient0 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient0) ∧
(Internal.selectionCofactorCoefficient1 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient1) ∧
(Internal.selectionCofactorCoefficient2 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient2) ∧
(Internal.selectionCofactorCoefficient3 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient3) ∧
(Internal.selectionCofactorCoefficient4 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient4) ∧
(Internal.selectionCofactorCoefficient5 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient5) := by
  exact ⟨MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner0, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner1, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner2, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner3, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner4, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner5⟩

#print axioms solution
