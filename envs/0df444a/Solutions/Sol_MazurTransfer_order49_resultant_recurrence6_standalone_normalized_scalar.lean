-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_standalone_normalized_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T21:07:54.367981+00:00
-- url     : https://prove2.me/submissions/60fc718c-6fa9-4b0d-9bf1-a387fc804c6c

import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_standalone_arithmetic_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_standalone_arithmetic_1
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_standalone_arithmetic_2
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_standalone_arithmetic_3
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_standalone_arithmetic_4
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_standalone_arithmetic_5
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_standalone_arithmetic_6
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_standalone_arithmetic_7
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_standalone_arithmetic_8
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
open Polynomial
open MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate
theorem solution :
remainder7Coefficient1Normalized ^ 2 *
        remainder6Coefficient0Normalized =
      remainder7Coefficient0Normalized *
          (remainder7Coefficient1Normalized *
              remainder6Coefficient1Normalized -
            remainder7Coefficient0Normalized *
              remainder6Coefficient2Normalized) -
        remainder6Coefficient2Normalized ^ 2 *
          normalizedExceptional6 := by
  have h0 := MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_0
  have h1 := MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_1
  have h2 := MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_2
  have h3 := MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_3
  have h4 := MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_4
  have h5 := MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_5
  have h6 := MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_6
  have h7 := MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_7
  have h8 := MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_8
  calc
    remainder7Coefficient1Normalized ^ 2 * remainder6Coefficient0Normalized =
        remainder7Coefficient1Square * remainder6Coefficient0Normalized := by
          rw [pow_two, h7]
    _ = normalizedResidual6Term1 := by simpa only [mul_comm] using h1
    _ = normalizedResidual6Term2 - normalizedResidual6Term3 := by
          linear_combination h4
    _ = remainder7Coefficient0Normalized * normalizedResidual6Inner -
        remainder6Coefficient2Square * normalizedExceptional6 := by
          rw [← h2, ← h3]
          ring
    _ = remainder7Coefficient0Normalized *
        (remainder7Coefficient1TimesRemainder6Coefficient1 -
          remainder7Coefficient0TimesRemainder6Coefficient2) -
        remainder6Coefficient2Square * normalizedExceptional6 := by
          rw [← h0]
          ring
    _ = remainder7Coefficient0Normalized *
        (remainder7Coefficient1Normalized * remainder6Coefficient1Normalized -
          remainder7Coefficient0Normalized * remainder6Coefficient2Normalized) -
        remainder6Coefficient2Square * normalizedExceptional6 := by rw [h8, h6]
    _ = remainder7Coefficient0Normalized *
        (remainder7Coefficient1Normalized * remainder6Coefficient1Normalized -
          remainder7Coefficient0Normalized * remainder6Coefficient2Normalized) -
        remainder6Coefficient2Normalized ^ 2 * normalizedExceptional6 := by rw [pow_two, h5]
#print axioms solution
