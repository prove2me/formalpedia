-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_8
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:01:31.398726+00:00
-- url     : https://prove2.me/submissions/bab3ca2e-6013-4840-a769-e4d416fa42ff

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 256).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 256).take 32 := by decide +kernel
#print axioms solution
