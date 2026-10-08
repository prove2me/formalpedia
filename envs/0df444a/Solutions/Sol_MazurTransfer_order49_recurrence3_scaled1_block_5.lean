-- Prove2me | solution 1 for MazurTransfer.order49_recurrence3_scaled1_block_5
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T23:43:21.892814+00:00
-- url     : https://prove2.me/submissions/4bc50bd8-3198-42dc-815e-9ef1abc8a8a4

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Mathlib.Data.List.TakeDrop
theorem solution : (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledLeft.drop 160).take 32 = (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalar1ScaledRight.drop 160).take 32 := by decide +kernel
#print axioms solution
