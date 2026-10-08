-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_7
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:04:15.507001+00:00
-- url     : https://prove2.me/submissions/84889bef-10f8-4237-97dd-62a23b8c956a

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 224).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 224).take 32 := by decide +kernel
#print axioms solution
