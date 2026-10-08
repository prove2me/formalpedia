-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_normalized_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T20:54:35.686056+00:00
-- url     : https://prove2.me/submissions/745c83cb-7c6d-44fa-bb7c-fde9ffded4b2

import Theorems.Thm_MazurTransfer_order49_resultant_recurrence6_standalone_normalized_scalar
import Definitions.Def_MazurTransfer_Order49Recurrence6NormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
theorem normalized_value_preserved_0 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0Normalized = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0Normalized := by rfl
theorem normalized_value_preserved_1 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1Normalized = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient1Normalized := by rfl
theorem normalized_value_preserved_2 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Normalized = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient2Normalized := by rfl
theorem normalized_value_preserved_3 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0Normalized = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0Normalized := by rfl
theorem normalized_value_preserved_4 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Normalized = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1Normalized := by rfl
theorem normalized_value_preserved_5 : MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedExceptional6 = MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedExceptional6 := by rfl
#print axioms normalized_value_preserved_0
#print axioms normalized_value_preserved_1
#print axioms normalized_value_preserved_2
#print axioms normalized_value_preserved_3
#print axioms normalized_value_preserved_4
#print axioms normalized_value_preserved_5

open Polynomial
open MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate
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
  rw [normalized_value_preserved_0, normalized_value_preserved_1, normalized_value_preserved_2, normalized_value_preserved_3, normalized_value_preserved_4, normalized_value_preserved_5]
  exact MazurTransfer.order49_resultant_recurrence6_standalone_normalized_scalar
#print axioms solution
