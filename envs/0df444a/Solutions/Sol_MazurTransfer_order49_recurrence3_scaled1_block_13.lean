-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_13
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T00:11:55.436824+00:00
-- url     : https://prove2.me/submissions/d64094ad-2705-4fe1-ae7d-0b1d39e4cbfb

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 416).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 416).take 32 := by decide +kernel
#print axioms solution
