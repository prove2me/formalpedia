-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_14
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:41:02.0667+00:00
-- url     : https://prove2.me/submissions/0d2468de-297f-4a6b-9a1b-227264f644e7

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 448).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 448).take 32 := by decide +kernel
#print axioms solution
