-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled2_block_10
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:06:24.640356+00:00
-- url     : https://prove2.me/submissions/5d932492-3049-4b69-a426-3e8b05032f12

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledLeft.drop 320).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar2ScaledRight.drop 320).take 32 := by decide +kernel
#print axioms solution
