-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:18:43.215197+00:00
-- url     : https://prove2.me/submissions/310e80fd-62db-406a-a347-04bf7b02271d

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 0).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 0).take 32 := by decide +kernel
#print axioms solution
