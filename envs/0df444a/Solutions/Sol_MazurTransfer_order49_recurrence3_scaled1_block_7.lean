-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_7
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:52:41.512204+00:00
-- url     : https://prove2.me/submissions/6336647b-9797-4eea-b25f-e42cf7ff485a

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 224).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 224).take 32 := by decide +kernel
#print axioms solution
