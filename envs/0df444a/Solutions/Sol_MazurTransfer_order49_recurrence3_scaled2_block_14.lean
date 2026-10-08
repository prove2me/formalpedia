-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_14
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:37:05.52778+00:00
-- url     : https://prove2.me/submissions/d4f2d5d6-854f-4938-8400-202180a5cf88

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 448).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 448).take 32 := by decide +kernel
#print axioms solution
