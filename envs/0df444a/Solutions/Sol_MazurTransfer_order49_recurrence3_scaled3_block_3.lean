-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_3
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:52:26.642891+00:00
-- url     : https://prove2.me/submissions/66902a68-618a-4099-9187-b963fafee53c

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 96).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 96).take 32 := by decide +kernel
#print axioms solution
