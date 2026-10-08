-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence0_inner_block_2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:21:08.2772+00:00
-- url     : https://prove2.me/submissions/f5ef9ed2-6825-421c-90fa-251325ba252c

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


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart2. Original headers retained. -/
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

theorem recurrence0Inner12 :
    Internal.selectionCofactorCoefficient12 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient5 := by
  unfold Internal.selectionCofactorCoefficient12
    Internal.selectionCofactorCoefficient12Chunk6
    Internal.selectionCofactorCoefficient12Chunk5
    Internal.selectionCofactorCoefficient12Chunk4
    Internal.selectionCofactorCoefficient12Chunk3
    Internal.selectionCofactorCoefficient12Chunk2
    Internal.selectionCofactorCoefficient12Chunk1
    Internal.selectionCofactorCoefficient12Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
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
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
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
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
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
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
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
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
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
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
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
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
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
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner13 :
    Internal.selectionCofactorCoefficient13 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient6 := by
  unfold Internal.selectionCofactorCoefficient13
    Internal.selectionCofactorCoefficient13Chunk6
    Internal.selectionCofactorCoefficient13Chunk5
    Internal.selectionCofactorCoefficient13Chunk4
    Internal.selectionCofactorCoefficient13Chunk3
    Internal.selectionCofactorCoefficient13Chunk2
    Internal.selectionCofactorCoefficient13Chunk1
    Internal.selectionCofactorCoefficient13Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
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
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
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
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
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
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
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
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
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
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
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
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner14 :
    Internal.selectionCofactorCoefficient14 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient7 := by
  unfold Internal.selectionCofactorCoefficient14
    Internal.selectionCofactorCoefficient14Chunk6
    Internal.selectionCofactorCoefficient14Chunk5
    Internal.selectionCofactorCoefficient14Chunk4
    Internal.selectionCofactorCoefficient14Chunk3
    Internal.selectionCofactorCoefficient14Chunk2
    Internal.selectionCofactorCoefficient14Chunk1
    Internal.selectionCofactorCoefficient14Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
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
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
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
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
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
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
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
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
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
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner15 :
    Internal.selectionCofactorCoefficient15 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient8 := by
  unfold Internal.selectionCofactorCoefficient15
    Internal.selectionCofactorCoefficient15Chunk6
    Internal.selectionCofactorCoefficient15Chunk5
    Internal.selectionCofactorCoefficient15Chunk4
    Internal.selectionCofactorCoefficient15Chunk3
    Internal.selectionCofactorCoefficient15Chunk2
    Internal.selectionCofactorCoefficient15Chunk1
    Internal.selectionCofactorCoefficient15Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
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
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
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
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
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
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
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
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner16 :
    Internal.selectionCofactorCoefficient16 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient9 := by
  unfold Internal.selectionCofactorCoefficient16
    Internal.selectionCofactorCoefficient16Chunk5
    Internal.selectionCofactorCoefficient16Chunk4
    Internal.selectionCofactorCoefficient16Chunk3
    Internal.selectionCofactorCoefficient16Chunk2
    Internal.selectionCofactorCoefficient16Chunk1
    Internal.selectionCofactorCoefficient16Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
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
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
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
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
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
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner17 :
    Internal.selectionCofactorCoefficient17 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient10 := by
  unfold Internal.selectionCofactorCoefficient17
    Internal.selectionCofactorCoefficient17Chunk5
    Internal.selectionCofactorCoefficient17Chunk4
    Internal.selectionCofactorCoefficient17Chunk3
    Internal.selectionCofactorCoefficient17Chunk2
    Internal.selectionCofactorCoefficient17Chunk1
    Internal.selectionCofactorCoefficient17Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
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
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
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
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end

open Polynomial MazurTorsion.Kubert.OrderSevenBacktrackingCertificate MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem solution :
(Internal.selectionCofactorCoefficient12 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient5) ∧
(Internal.selectionCofactorCoefficient13 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient6) ∧
(Internal.selectionCofactorCoefficient14 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient7) ∧
(Internal.selectionCofactorCoefficient15 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient8) ∧
(Internal.selectionCofactorCoefficient16 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient9) ∧
(Internal.selectionCofactorCoefficient17 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient10) := by
  exact ⟨MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner12, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner13, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner14, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner15, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner16, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner17⟩

#print axioms solution
