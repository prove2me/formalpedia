-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_1
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:23:39.316971+00:00
-- url     : https://prove2.me/submissions/e0a51aed-39ba-4211-b754-985ee6755de5

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 32).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 32).take 32 := by decide +kernel
#print axioms solution
