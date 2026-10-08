-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_9
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:09:18.13633+00:00
-- url     : https://prove2.me/submissions/bb4ced23-f58e-4a0f-a583-2c140a3e83c9

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 288).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 288).take 32 := by decide +kernel
#print axioms solution
