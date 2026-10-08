-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence0_inner_block_3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:25:33.728591+00:00
-- url     : https://prove2.me/submissions/07dc041e-00c6-46ec-bdb5-3e3e53b3e298

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


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart3. Original headers retained. -/
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

theorem recurrence0Inner18 :
    Internal.selectionCofactorCoefficient18 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient11 := by
  unfold Internal.selectionCofactorCoefficient18
    Internal.selectionCofactorCoefficient18Chunk5
    Internal.selectionCofactorCoefficient18Chunk4
    Internal.selectionCofactorCoefficient18Chunk3
    Internal.selectionCofactorCoefficient18Chunk2
    Internal.selectionCofactorCoefficient18Chunk1
    Internal.selectionCofactorCoefficient18Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
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
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner19 :
    Internal.selectionCofactorCoefficient19 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient12 := by
  unfold Internal.selectionCofactorCoefficient19
    Internal.selectionCofactorCoefficient19Chunk4
    Internal.selectionCofactorCoefficient19Chunk3
    Internal.selectionCofactorCoefficient19Chunk2
    Internal.selectionCofactorCoefficient19Chunk1
    Internal.selectionCofactorCoefficient19Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient12
    quotient0Coefficient12Block0
    quotient0Coefficient12Chunk6
    quotient0Coefficient12Chunk5
    quotient0Coefficient12Chunk4
    quotient0Coefficient12Chunk3
    quotient0Coefficient12Chunk2
    quotient0Coefficient12Chunk1
    quotient0Coefficient12Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner20 :
    Internal.selectionCofactorCoefficient20 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient13 := by
  unfold Internal.selectionCofactorCoefficient20
    Internal.selectionCofactorCoefficient20Chunk4
    Internal.selectionCofactorCoefficient20Chunk3
    Internal.selectionCofactorCoefficient20Chunk2
    Internal.selectionCofactorCoefficient20Chunk1
    Internal.selectionCofactorCoefficient20Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient20
    quotient0Coefficient20Block0
    quotient0Coefficient20Chunk3
    quotient0Coefficient20Chunk2
    quotient0Coefficient20Chunk1
    quotient0Coefficient20Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient13
    quotient0Coefficient13Block0
    quotient0Coefficient13Chunk6
    quotient0Coefficient13Chunk5
    quotient0Coefficient13Chunk4
    quotient0Coefficient13Chunk3
    quotient0Coefficient13Chunk2
    quotient0Coefficient13Chunk1
    quotient0Coefficient13Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner21 :
    Internal.selectionCofactorCoefficient21 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient14 := by
  unfold Internal.selectionCofactorCoefficient21
    Internal.selectionCofactorCoefficient21Chunk4
    Internal.selectionCofactorCoefficient21Chunk3
    Internal.selectionCofactorCoefficient21Chunk2
    Internal.selectionCofactorCoefficient21Chunk1
    Internal.selectionCofactorCoefficient21Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient21
    quotient0Coefficient21Block0
    quotient0Coefficient21Chunk2
    quotient0Coefficient21Chunk1
    quotient0Coefficient21Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient20
    quotient0Coefficient20Block0
    quotient0Coefficient20Chunk3
    quotient0Coefficient20Chunk2
    quotient0Coefficient20Chunk1
    quotient0Coefficient20Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient14
    quotient0Coefficient14Block0
    quotient0Coefficient14Chunk6
    quotient0Coefficient14Chunk5
    quotient0Coefficient14Chunk4
    quotient0Coefficient14Chunk3
    quotient0Coefficient14Chunk2
    quotient0Coefficient14Chunk1
    quotient0Coefficient14Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner22 :
    Internal.selectionCofactorCoefficient22 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient15 := by
  unfold Internal.selectionCofactorCoefficient22
    Internal.selectionCofactorCoefficient22Chunk3
    Internal.selectionCofactorCoefficient22Chunk2
    Internal.selectionCofactorCoefficient22Chunk1
    Internal.selectionCofactorCoefficient22Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient22
    quotient0Coefficient22Block0
    quotient0Coefficient22Chunk2
    quotient0Coefficient22Chunk1
    quotient0Coefficient22Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient21
    quotient0Coefficient21Block0
    quotient0Coefficient21Chunk2
    quotient0Coefficient21Chunk1
    quotient0Coefficient21Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient20
    quotient0Coefficient20Block0
    quotient0Coefficient20Chunk3
    quotient0Coefficient20Chunk2
    quotient0Coefficient20Chunk1
    quotient0Coefficient20Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient15
    quotient0Coefficient15Block0
    quotient0Coefficient15Chunk5
    quotient0Coefficient15Chunk4
    quotient0Coefficient15Chunk3
    quotient0Coefficient15Chunk2
    quotient0Coefficient15Chunk1
    quotient0Coefficient15Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
theorem recurrence0Inner23 :
    Internal.selectionCofactorCoefficient23 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient16 := by
  unfold Internal.selectionCofactorCoefficient23
    Internal.selectionCofactorCoefficient23Chunk3
    Internal.selectionCofactorCoefficient23Chunk2
    Internal.selectionCofactorCoefficient23Chunk1
    Internal.selectionCofactorCoefficient23Chunk0
    Internal.divisionCofactor0Coefficient0
    Internal.divisionCofactor0Coefficient0Chunk2
    Internal.divisionCofactor0Coefficient0Chunk1
    Internal.divisionCofactor0Coefficient0Chunk0
    quotient0Coefficient23
    quotient0Coefficient23Block0
    quotient0Coefficient23Chunk1
    quotient0Coefficient23Chunk0
    Internal.divisionCofactor0Coefficient1
    Internal.divisionCofactor0Coefficient1Chunk1
    Internal.divisionCofactor0Coefficient1Chunk0
    quotient0Coefficient22
    quotient0Coefficient22Block0
    quotient0Coefficient22Chunk2
    quotient0Coefficient22Chunk1
    quotient0Coefficient22Chunk0
    Internal.divisionCofactor0Coefficient2
    Internal.divisionCofactor0Coefficient2Chunk1
    Internal.divisionCofactor0Coefficient2Chunk0
    quotient0Coefficient21
    quotient0Coefficient21Block0
    quotient0Coefficient21Chunk2
    quotient0Coefficient21Chunk1
    quotient0Coefficient21Chunk0
    Internal.divisionCofactor0Coefficient3
    Internal.divisionCofactor0Coefficient3Chunk1
    Internal.divisionCofactor0Coefficient3Chunk0
    quotient0Coefficient20
    quotient0Coefficient20Block0
    quotient0Coefficient20Chunk3
    quotient0Coefficient20Chunk2
    quotient0Coefficient20Chunk1
    quotient0Coefficient20Chunk0
    Internal.divisionCofactor0Coefficient4
    Internal.divisionCofactor0Coefficient4Chunk0
    quotient0Coefficient19
    quotient0Coefficient19Block0
    quotient0Coefficient19Chunk3
    quotient0Coefficient19Chunk2
    quotient0Coefficient19Chunk1
    quotient0Coefficient19Chunk0
    Internal.divisionCofactor0Coefficient5
    Internal.divisionCofactor0Coefficient5Chunk0
    quotient0Coefficient18
    quotient0Coefficient18Block0
    quotient0Coefficient18Chunk4
    quotient0Coefficient18Chunk3
    quotient0Coefficient18Chunk2
    quotient0Coefficient18Chunk1
    quotient0Coefficient18Chunk0
    Internal.divisionCofactor0Coefficient6
    Internal.divisionCofactor0Coefficient6Chunk0
    quotient0Coefficient17
    quotient0Coefficient17Block0
    quotient0Coefficient17Chunk4
    quotient0Coefficient17Chunk3
    quotient0Coefficient17Chunk2
    quotient0Coefficient17Chunk1
    quotient0Coefficient17Chunk0
    Internal.divisionCofactor0Coefficient7
    Internal.divisionCofactor0Coefficient7Chunk0
    quotient0Coefficient16
    quotient0Coefficient16Block0
    quotient0Coefficient16Chunk5
    quotient0Coefficient16Chunk4
    quotient0Coefficient16Chunk3
    quotient0Coefficient16Chunk2
    quotient0Coefficient16Chunk1
    quotient0Coefficient16Chunk0
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_1]
  ring
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end

open Polynomial MazurTorsion.Kubert.OrderSevenBacktrackingCertificate MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem solution :
(Internal.selectionCofactorCoefficient18 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient11) ∧
(Internal.selectionCofactorCoefficient19 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient12) ∧
(Internal.selectionCofactorCoefficient20 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient13) ∧
(Internal.selectionCofactorCoefficient21 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient14) ∧
(Internal.selectionCofactorCoefficient22 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient15) ∧
(Internal.selectionCofactorCoefficient23 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient16) := by
  exact ⟨MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner18, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner19, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner20, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner21, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner22, MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0Inner23⟩

#print axioms solution
