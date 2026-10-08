-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled3_block_10
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:11:25.9704+00:00
-- url     : https://prove2.me/submissions/585bc469-2050-4c74-978b-4274314fc76b

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledLeft.drop 320).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar3ScaledRight.drop 320).take 32 := by decide +kernel
#print axioms solution
