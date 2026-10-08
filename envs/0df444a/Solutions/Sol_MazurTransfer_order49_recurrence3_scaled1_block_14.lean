-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_14
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:14:51.841764+00:00
-- url     : https://prove2.me/submissions/bf922246-e7c0-4b0f-a361-1d2db1f2efdd

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 448).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 448).take 32 := by decide +kernel
#print axioms solution
