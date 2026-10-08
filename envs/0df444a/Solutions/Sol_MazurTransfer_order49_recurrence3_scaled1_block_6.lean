-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_6
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:48:21.029378+00:00
-- url     : https://prove2.me/submissions/9f8045cb-68b1-4dea-bec3-500e16506c83

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 192).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 192).take 32 := by decide +kernel
#print axioms solution
