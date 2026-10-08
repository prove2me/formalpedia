-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_13
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:34:19.875781+00:00
-- url     : https://prove2.me/submissions/bd83001b-3aed-4cd3-b8f1-fb3b56cdcef1

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 416).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 416).take 32 := by decide +kernel
#print axioms solution
