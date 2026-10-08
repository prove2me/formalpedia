-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_4
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:39:05.643323+00:00
-- url     : https://prove2.me/submissions/cf0bb150-82a4-4a7f-95d3-e19710d43a89

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 128).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 128).take 32 := by decide +kernel
#print axioms solution
