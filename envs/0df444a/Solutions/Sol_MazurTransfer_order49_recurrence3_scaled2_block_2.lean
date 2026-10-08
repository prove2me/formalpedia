-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_2
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:51:15.347515+00:00
-- url     : https://prove2.me/submissions/c22b5deb-cee9-4295-9489-3af5a11cb548

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 64).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 64).take 32 := by decide +kernel
#print axioms solution
