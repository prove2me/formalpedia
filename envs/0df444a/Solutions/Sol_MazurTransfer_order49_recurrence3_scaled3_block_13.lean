-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_13
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:38:35.689341+00:00
-- url     : https://prove2.me/submissions/bf873984-bd92-4f10-8413-1c84e01286f5

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 416).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 416).take 32 := by decide +kernel
#print axioms solution
