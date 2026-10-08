-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_15
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:43:05.953765+00:00
-- url     : https://prove2.me/submissions/3c5c39ef-0c0e-4bb9-a001-06bfba263094

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 480).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 480).take 32 := by decide +kernel
#print axioms solution
