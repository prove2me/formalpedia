-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_9
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:03:34.842038+00:00
-- url     : https://prove2.me/submissions/3c34e293-609a-4388-ac6a-bf55a8968e18

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 288).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 288).take 32 := by decide +kernel
#print axioms solution
