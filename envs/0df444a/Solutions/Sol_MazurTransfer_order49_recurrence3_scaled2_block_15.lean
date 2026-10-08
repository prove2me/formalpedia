-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_15
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:40:31.655146+00:00
-- url     : https://prove2.me/submissions/63fcb6d2-e930-4503-a141-f74458e2c636

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 480).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 480).take 32 := by decide +kernel
#print axioms solution
