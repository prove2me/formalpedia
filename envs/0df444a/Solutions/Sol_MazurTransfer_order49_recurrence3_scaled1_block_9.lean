-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_9
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:57:24.777494+00:00
-- url     : https://prove2.me/submissions/7c992fa0-5d5d-4ba0-b9b5-6434074fe3c6

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 288).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 288).take 32 := by decide +kernel
#print axioms solution
