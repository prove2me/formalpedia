-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:50:03.352646+00:00
-- url     : https://prove2.me/submissions/3109e38b-27b5-4ece-a1fb-d93eb45a6b05

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 32).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 32).take 32 := by decide +kernel
#print axioms solution
